from ca import CA
from node import Node
from cacher import Cacher
import smt_util
from typing import List
from typing import Set
from sim_config import SimConfig
import random
import logging
from tqdm import tqdm
import time
import sys
import copy


class BigNetSim:
    def __init__(self, config):
        random.seed()  # set a number for repeatable debugging
        logging.basicConfig(level=logging.WARNING)

        # measurements vars
        self.total_revokes = 0
        self.failed_repairs = 0
        self.successful_repairs = 0
        self.lvlc_repairs = 0
        self.repair_try_aggr = 0
        self.prime_successes = 0
        self.parity_fails = 0
        self.encounters_both_no_poi = 0
        self.total_encounters = 0

        # msg sizes
        self.msg_sizes_all = 0
        self.msg_sizes_repair = 0
        self.msg_sizes_update = 0
        self.msg_sizes_ca_out = 0
        self.msg_sizes_ca_out_lvlc = 0
        self.update_count = 0
        self.aggr_update_size = 0
        self.prune_count = 0
        self.aggr_prune_size = 0

        # initialize ca
        self.c = config
        self.smtu = smt_util.SMTutil(self.c.hash_function, self.c.hash_depth)
        self.ca = CA(self.c)
        self.all_nodes: List[Node] = []
        self.revoked_nodes: List[Node] = []

        logging.info('setting up CA...')
        self.ca.initialize()
        prime_root = self.ca.get_prime()
        smt_roots = self.ca.get_smt_roots()
        lvl_caches = self.ca.get_lvl_caches(self.c.cache_level)

        # initialize nodes
        logging.info('initializing active nodes...')
        # check for unfilled cache elements -> incomplete lvl-cache
        for c in lvl_caches:
            for h in c:
                if h == '':
                    logging.error('unfilled cache element found!')
                    sys.exit(-1)
        for i in tqdm(range(self.c.no_cacher)):
            smt_part = i % self.c.no_smt_parts
            poi, poi_bm = self.ca.get_node_poi(i, smt_part)
            node = Cacher(self.c.cache_level, copy.deepcopy(lvl_caches), i, smt_part,
                          poi, poi_bm, smt_roots.copy(), copy.deepcopy(prime_root), self.c)
            self.all_nodes.append(node)

        for i in tqdm(range(self.c.no_cacher, self.c.start_no_nodes)):
            smt_part = i % self.c.no_smt_parts
            poi, poi_bm = self.ca.get_node_poi(i, smt_part)
            node = Node(i, smt_part, poi, poi_bm, smt_roots.copy(), copy.deepcopy(prime_root), self.c)
            self.all_nodes.append(node)

    def sim(self):
        sub_epoch = 1
        for current_time_step in tqdm(range(self.c.total_time_steps)):
            ##### each epoch action
            if sub_epoch % self.c.subs_per_epoch == 0:
                sub_epoch += 1
                # update ca
                self.ca.epoch_tree_change()
                # update all nodes
                self.epoch_update_nodes()
                # insert new certs
                self.issue_new_certs()

            ##### each sub_epoch action
            if current_time_step % self.c.time_steps_per_sub_epoch == 0:
                sub_epoch += 1
                # issue new certs for revoked nodes
                self.ca.reissue_nodes(self.revoked_nodes)

                # revoke some nodes
                revoke_nodes: List[Node] = random.sample(self.all_nodes, self.c.revoked_per_sub_epoch)
                # skip just re-issued nodes
                revoke_nodes = [x for x in revoke_nodes if x not in self.revoked_nodes]
                self.ca.revoke_nodes(revoke_nodes)
                self.total_revokes += len(revoke_nodes)

                # construct & send update
                update = self.ca.construct_update(self.revoked_nodes, False)
                update.extend(self.ca.construct_update(revoke_nodes, True))

                # list for directly updating changed nodes
                to_update_nodes = self.revoked_nodes.copy()
                to_update_nodes.extend(revoke_nodes)
                self.revoked_nodes.clear()  # remove re-issued nodes
                self.revoked_nodes = revoke_nodes.copy()  # add freshly revoked nodes
                revoke_nodes.clear()
                # send update to all nodes
                self.send_update(update, to_update_nodes)
                logging.info(f'sent update containing {len(update)} update-pois')

            ##### each time_step action: nodes encounter other nodes
            self.total_encounters += self.c.encounters_per_node * len(self.all_nodes)
            for n in self.all_nodes:
                # skip if no updates needed
                if not n.outdated_prime and not n.outdated_poi:
                    if not isinstance(n, Cacher) or not n.outdated_lvlc:
                        continue

                # random encounters
                encounters: List[Node] = random.sample(self.all_nodes, self.c.encounters_per_node)
                for e in encounters:
                    if e == n:  # happens sometimes...
                        continue
                    # MSGs basic prime encounter exchange, always happens
                    self.msg_sizes_all += self.c.msg_size_prime_root
                    # check if both are outdated -> no secure channel possible
                    if e.outdated_poi and not e.outdated_prime and n.outdated_poi and not n.outdated_prime:
                        self.encounters_both_no_poi += 1
                    # node cannot help me if he's not fresh at all
                    if e.outdated_prime:
                        continue

                    # update prime root
                    if n.outdated_prime:
                        self.update_prime(n, e)

                    if isinstance(n, Cacher) and n.outdated_lvlc:
                        n.update_try_lvlc += 1
                        # update level-cache directly
                        if isinstance(e, Cacher) and not e.outdated_lvlc:
                            self.update_lvl_cache(n, e)
                        # update level-cache via poi
                        # -> TONS of overhead, is commented for performance, as virtually no improvement
                        # elif not e.outdated_poi:
                        #     self.update_lvl_cache_with_poi(n, e)

                    if self.c.sanity_checks:
                        outdated_poi = self.ca.get_node_poi(n.node_id, n.smt_part) != (n.poi, n.poi_bm)
                        if outdated_poi and not n.outdated_poi and not n.revoked:
                            logging.error(f'Node thinks its poi is good, but is not! node: {n}')
                            logging.error(f'prime is {n.prime_root == self.ca.prime_root}')
                            logging.error(f'real root is {self.ca.get_smt_roots()[n.smt_part]}, '
                                          f'node root is {n.smt_roots[n.smt_part]}')
                            logging.error(f'real poi: {self.ca.get_node_poi(n.node_id, n.smt_part)}')
                            logging.error(f'node poi: {n.poi}, bm: {n.poi_bm}')
                            logging.error(f'prev poi: {n.previous_poi}, bm: {n.previous_poi_bm}')
                            logging.error(f'prup poi: {n.previous_update_poi}, '
                                          f'bm: {n.previous_update_poi_bm}, cert: {n.previous_update_hash}, '
                                          f'revoked: {n.previous_update_revoked}')

                    # distributed repair of poi
                    if n.outdated_poi:
                        if not n.revoked:
                            n.update_try += 1
                    else:
                        continue

                    # update poi via lvl-cache
                    if isinstance(e, Cacher) and not n.lvl_cache_tried and not e.outdated_lvlc:
                        self.repair_via_lvlc(n, e)

                    # update poi via other poi, if in same part
                    if n.outdated_poi and not e.outdated_poi and e.smt_part == n.smt_part and \
                            (not n.revoked or not e.revoked):
                        self.repair_via_poi(n, e)

                # if try threshold is reached, give up, force repair via CA & reset node
                if n.outdated_poi and n.update_try > self.c.max_repair_tries:
                    logging.info('node reached max tries for repair...')
                    self.reset_outdated(n)
                    # if isinstance(n, BnsCacher) and n.outdated_lvlc:
                    #     self.reset_outdated_cacher(n)
                    self.failed_repairs += 1
                # Separate failsafe for cache leads to CA sending out tons of data, with virutally no improvement
                if isinstance(n, Cacher) and n.outdated_lvlc and n.update_try_lvlc > self.c.max_repair_tries:
                    self.reset_outdated_cacher(n)

        ##### ALL DONE: print final evaluation
        print(f'total revocations: {self.total_revokes} ({self.total_revokes / self.c.start_no_nodes * 100:1.2f}%)')
        print(f'total nodes needed repairs: {self.successful_repairs + self.failed_repairs}')
        print(f'successful repairs: {self.successful_repairs}, '
              f'lvlc: {self.lvlc_repairs} ({self.lvlc_repairs / self.successful_repairs * 100:1.2f}%), '
              f'avg. try: {self.repair_try_aggr / self.successful_repairs:1.2f}')
        print(f'failed repairs: {self.failed_repairs} '
              f'({self.failed_repairs / (self.failed_repairs + self.successful_repairs) * 100:1.2f}%)')
        print(f'Avg. size per update {self.aggr_update_size / self.update_count / 1024:1.2f} KB')
        print(f'CA sent out '
              f'{self.msg_sizes_ca_out / (self.c.epochs * self.c.subs_per_epoch) / 1024:1.2f} KB per day '
              f'({self.msg_sizes_ca_out_lvlc / self.msg_sizes_ca_out * 100:1.2f}% for caches)')
        msgs_all = self.msg_sizes_all / self.c.start_no_nodes
        print(f'Each nodes sent {msgs_all / self.c.epochs / 1024:1.2f} KB on avg. per week')
        msgs_repair = self.msg_sizes_repair / self.c.start_no_nodes
        print(f'For repairs, each node sent {msgs_repair / self.c.epochs / 1024:1.2f} KB on avg. per week '
              f'({msgs_repair / msgs_all * 100:1.2f}%)')
        print(f'Nodes having prime root parity fails: {self.parity_fails} '
              f'({self.parity_fails / (self.parity_fails + self.prime_successes) * 100:1.6f}%)')
        print(f'Avg. prune update size: {self.aggr_prune_size / self.prune_count / 1024:1.2f} KB')
        print(f'Total encounters: {self.total_encounters}')
        print(f'Number of encounters where both nodes are outdated: {self.encounters_both_no_poi} ('
              f'{self.encounters_both_no_poi / self.total_encounters * 100:1.6f}%)')

        ##### return evaluation results
        result = [self.total_revokes,  # total_revocations
                  self.successful_repairs + self.failed_repairs,  # total_n_needed_repairs
                  self.repair_try_aggr / self.successful_repairs,  # avg_try
                  self.lvlc_repairs / self.successful_repairs * 100,  # lvlc_share_perc
                  self.failed_repairs / (self.failed_repairs + self.successful_repairs) * 100,  # failed_repairs_perc
                  self.aggr_update_size / self.update_count / 1024,  # avg_update_size_bytes
                  msgs_all / self.c.epochs / 1024,  # nodes_sent_per_week_bytes
                  msgs_repair / msgs_all * 100,  # nodes_sent_repair_share_perc
                  self.parity_fails / (self.parity_fails + self.prime_successes) * 100,  # parity_fails_share_perc
                  self.aggr_prune_size / self.prune_count / 1024,  # avg_prune_update_size_bytes
                  self.total_encounters,  # total_encounters
                  self.encounters_both_no_poi / self.total_encounters * 100  # encounters_both_outdated_share_perc
                  ]
        return result

    def send_update(self, update, to_update_nodes):
        # update = [(part, hash, poi, bm, revoked)]

        # check affected smt parts
        smt_roots = copy.deepcopy(self.ca.get_smt_roots())
        affected_smts = []  # [(part, root)]
        affected_parts = []  # [part]
        update_per_part = [[] for _ in range(self.c.no_smt_parts)]
        unique_hashes = self.ca.get_unique_hash_count(update)
        for u in update:
            if u[0] not in affected_parts:
                affected_parts.append(u[0])
                affected_smts.append((u[0], smt_roots[u[0]]))
            update_per_part[u[0]].append(u)

        # select nodes that miss update
        non_updated_nodes = random.sample(self.all_nodes, self.c.no_missing_nodes)
        # avoid nodes that are directly affected by an update
        non_updated_nodes: List[Node] = [x for x in non_updated_nodes if x not in to_update_nodes]
        update_count = len(self.all_nodes) - len(non_updated_nodes)
        cacher_count = 0

        # set missing nodes to outdated
        for n in non_updated_nodes:
            n.outdated_prime = True
        # send out updates
        for n in self.all_nodes:
            if n in non_updated_nodes:
                continue
            # update prime
            n.set_some_smt_roots(affected_smts)
            n.prime_root = self.ca.get_prime()
            n.outdated_prime = False
            # separate specific node update parts & cacher
            if self.c.sanity_checks:
                tmp_poi = copy.deepcopy(n.poi)
                tmp_poi_bm = n.poi_bm
            if isinstance(n, Cacher):
                cacher_count += 1
                update_fail = n.process_update(update)
            else:
                update_fail = n.process_update(update_per_part[n.smt_part])
            # sanity-check
            if self.c.sanity_checks and update_fail:
                poi, poi_bm = self.ca.get_node_poi(n.node_id, n.smt_part)
                path_root = self.smtu.calc_path_root(n.cert, poi, poi_bm, 0, n.revoked)
                path_root_reverse = self.smtu.calc_path_root(n.cert, poi, poi_bm, 0, not n.revoked)
                logging.error(f'-> TARGET poi_bm: {poi_bm}, poi: {poi}\n'
                              f'-> TARGET root: {self.ca.smts[n.smt_part].roothash}\n'
                              f'-> OLD    poi_bm {tmp_poi_bm}, poi: {tmp_poi}\n'
                              f'-> CA poi root: {path_root}, reverse revoke: {path_root_reverse}\n'
                              f'-> node: {n}\n'
                              f'-> prev poi: {n.previous_poi}, bm: {n.previous_poi_bm}\n'
                              f'-> prup poi: {n.previous_update_poi}, bm: {n.previous_update_poi_bm}, '
                              f'cert: {n.previous_update_hash}, revoked: {n.previous_update_revoked}, '
                              f'calc_root: {self.smtu.calc_path_root(n.previous_update_hash, n.previous_update_poi, n.previous_update_poi_bm, 0, n.previous_update_revoked)}\n'
                              f'-> update: {update_per_part[n.smt_part]}')
        # MSGs CA update
        self.update_count += update_count - cacher_count
        self.aggr_update_size += (update_count - cacher_count) * \
                                 (self.c.msg_size_prime_root + self.c.sig_size +
                                  (len(affected_smts) * self.c.hash_bytes) +
                                  # (len(unique_hashes) / len(affected_smts) * self.c.hash_bytes))
                                  (len(unique_hashes) * self.c.hash_bytes))
        # cacher updates
        self.update_count += cacher_count
        self.aggr_update_size += cacher_count * (self.c.msg_size_prime_root + self.c.sig_size +
                                                 (len(affected_smts) * self.c.hash_bytes) +
                                                 (len(unique_hashes) * self.c.hash_bytes))

    def epoch_update_nodes(self):
        oldest_nodes = []
        for n in self.all_nodes:
            old_smt_part = n.smt_part
            # identify affected nodes & change smt-part
            if n.smt_part == 0:
                n.smt_part = self.c.no_smt_parts - 1
                oldest_nodes.append(n)
            else:
                n.smt_part = n.smt_part - 1

            # check for outdated poi on node
            if n.smt_roots[old_smt_part] != self.ca.get_a_smt_root(n.smt_part):
                n.outdated_poi = True

            n.prime_root = copy.deepcopy(self.ca.get_prime())
            n.smt_roots = self.ca.get_smt_roots().copy()
            n.outdated_prime = False
            if isinstance(n, Cacher):
                n.lvl_caches = copy.deepcopy(self.ca.get_lvl_caches(self.c.cache_level))
                n.outdated_lvlc = False
                n.outdated_roots = []


        # MSGs prune-update -> sends all hashes of new smt
        self.msg_sizes_ca_out += len(oldest_nodes) * self.c.hash_bytes + self.c.msg_size_prime_root + self.c.sig_size
        self.prune_count += 1
        self.aggr_prune_size += len(oldest_nodes) * self.c.hash_bytes

    def issue_new_certs(self):
        # we only need to measure here, no need to impl
        self.msg_sizes_ca_out += self.c.new_issues_per_epoch * self.c.hash_bytes
        self.aggr_prune_size += self.c.new_issues_per_epoch * self.c.hash_bytes

    def update_prime(self, outdated, helper):
        wrong_aggr_par_parts, wrong_main_par_parts = outdated.set_prime_id_wrong_parts(helper.prime_root)
        selected_smt_roots = helper.get_ided_smt_roots(wrong_aggr_par_parts, wrong_main_par_parts)
        if outdated.set_ided_smt_roots(selected_smt_roots):
            self.prime_successes += 1
            # MSGs only exchanged roots
            self.msg_sizes_all += len(selected_smt_roots) * self.c.hash_bytes + self.c.sig_size
            self.msg_sizes_update += len(selected_smt_roots) * self.c.hash_bytes + self.c.sig_size
        else:
            # parity got unlucky, request all
            logging.info(f'prime root parity got unlucky, exchanged all roots')
            self.parity_fails += 1
            # check if poi is outdated
            if outdated.smt_roots[outdated.smt_part] != self.ca.get_a_smt_root(outdated.smt_part):
                outdated.outdated_poi = True
            # check if cache is outdated, add missing parts to outdated list
            if isinstance(outdated, Cacher):
                ca_roots = self.ca.get_smt_roots()
                for i in range(self.c.no_smt_parts):
                    if outdated.smt_roots[i] != ca_roots[i]:
                        outdated.outdated_roots.append(i)
                if len(outdated.outdated_roots) > 1:
                    outdated.outdated_lvlc = True
            # force update prime
            outdated.prime_root = copy.deepcopy(self.ca.get_prime())
            outdated.smt_roots = self.ca.get_smt_roots().copy()
            outdated.outdated_prime = False
            # MSGs prime exchange
            self.msg_sizes_all += self.c.no_smt_parts * self.c.hash_bytes + self.c.sig_size
            self.msg_sizes_update += self.c.no_smt_parts * self.c.hash_bytes + self.c.sig_size

    def update_lvl_cache(self, outdated, helper):
        outdated_lvl_caches = helper.get_some_lvl_caches(outdated.outdated_roots)
        outdated.update_some_lvl_caches(copy.deepcopy(outdated_lvl_caches))
        outdated.outdated_lvlc = False
        outdated.update_try_lvlc = 0
        outdated.outdated_roots = []
        # MSGs exchange cache
        self.msg_sizes_all += self.c.msg_size_lvlc * len(outdated_lvl_caches)
        self.msg_sizes_repair += self.c.msg_size_lvlc * len(outdated_lvl_caches)

    def update_lvl_cache_with_poi(self, outdated, helper):
        # update correct cache
        self.smtu.update_lvl_cache_with_poi(helper.cert, helper.poi, helper.poi_bm,
                                            outdated.lvl_caches[helper.smt_part], outdated.cache_level, helper.revoked)
        # check if cache is now good
        any_outdated = False
        for i in range(self.c.no_smt_parts):
            if outdated.smt_roots[i] != self.smtu.lvl_cache_helper(0, 0, outdated.lvl_caches[i], outdated.cache_level):
                any_outdated = True
        outdated.outdated_lvlc = any_outdated
        # MSGs
        self.msg_sizes_all += self.c.msg_size_poi
        self.msg_sizes_repair += self.c.msg_size_poi

    def repair_via_lvlc(self, outdated, helper):
        # MSGs exchange only poi -> repair on cacher
        self.msg_sizes_all += self.c.msg_size_poi * 2
        self.msg_sizes_repair += self.c.msg_size_poi * 2
        if self.c.sanity_checks:
            tmp_poi = copy.deepcopy(outdated.poi)
            tmp_poi_bm = outdated.poi_bm
        if outdated.try_lvlc_repair(helper.lvl_caches[outdated.smt_part], helper.cache_level):
            logging.info('successfully repaired node via LVLC')
            self.successful_repairs += 1
            self.lvlc_repairs += 1
            self.repair_try_aggr += outdated.update_try
            outdated.update_try = 0
            outdated.outdated_poi = False
            outdated.lvl_cache_tried = False
            if self.c.sanity_checks and self.ca.get_node_poi(outdated.node_id, outdated.smt_part) != (outdated.poi, outdated.poi_bm):
                logging.error(f'LVLC REPAIR FAILED for node {outdated} \n-> helped by {helper} \n'
                              f'old poi: {tmp_poi}; {tmp_poi_bm}\n'
                              f'hel lvlc: {helper.lvl_caches}\n'
                              f'tar poi: {self.ca.get_node_poi(outdated.node_id, outdated.smt_part)}')
        else:
            logging.info('failed to repair node via LVLC')
            outdated.lvl_cache_tried = True

    def repair_via_poi(self, outdated, helper):
        # MSGs exchange poi
        self.msg_sizes_all += self.c.msg_size_poi
        self.msg_sizes_repair += self.c.msg_size_poi
        if self.c.sanity_checks:
            tmp_poi = copy.deepcopy(outdated.poi)
            tmp_poi_bm = outdated.poi_bm
        if outdated.try_poi_repair(helper.cert, helper.poi, helper.poi_bm):
            logging.info('successfully repaired node via PoI')
            self.successful_repairs += 1
            self.repair_try_aggr += outdated.update_try
            outdated.update_try = 0
            outdated.outdated_poi = False
            outdated.lvl_cache_tried = False
            if self.c.sanity_checks and self.ca.get_node_poi(outdated.node_id, outdated.smt_part) != (outdated.poi, outdated.poi_bm):
                logging.error(f'POI REPAIR FAILED for node {outdated} \n-> helped by {helper} \n'
                              f'old poi: {tmp_poi}; {tmp_poi_bm}\n'
                              f'hel poi: {helper.poi}; {helper.poi_bm}\n'
                              f'tar poi: {self.ca.get_node_poi(outdated.node_id, outdated.smt_part)}')
            if self.c.sanity_checks:
                outdated.previous_update_hash = helper.cert
                outdated.previous_update_poi = helper.poi
                outdated.previous_update_poi_bm = helper.poi_bm
                outdated.previous_update_revoked = helper.previous_update_revoked
                outdated.previous_poi = tmp_poi
                outdated.previous_poi_bm = tmp_poi_bm
        else:
            logging.info('failed to repair node via PoI')

    def reset_outdated(self, node):
        # MSGs request poi from ca
        self.msg_sizes_ca_out += self.c.msg_size_poi
        # force repair & reset
        poi, poi_bm = self.ca.get_node_poi(node.node_id, node.smt_part)
        node.poi = poi
        node.poi_bm = poi_bm
        node.smt_roots = self.ca.get_smt_roots()
        node.prime_root = self.ca.get_prime()
        node.update_try = 0
        node.outdated_poi = False
        node.outdated_prime = False
        node.lvl_cache_tried = False

    def reset_outdated_cacher(self, node):
        outdated_lvl_caches = self.ca.get_some_lvl_caches(node.outdated_roots)
        node.update_some_lvl_caches(copy.deepcopy(outdated_lvl_caches))
        node.outdated_lvlc = False
        node.update_try_lvlc = 0
        node.outdated_roots = []
        # MSGs exchange cache
        self.msg_sizes_ca_out += self.c.msg_size_lvlc * len(outdated_lvl_caches)
        self.msg_sizes_ca_out_lvlc += self.c.msg_size_lvlc * len(outdated_lvl_caches)
