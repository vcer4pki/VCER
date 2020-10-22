from smt import SMT
from node import Node
import smt_util
import hashf
import sim_config
from tqdm import tqdm
import pickle
import logging
from typing import List
from os import path
import sys
import copy


class CA:
    def __init__(self, config):
        self.c: sim_config.SimConfig = config
        self.smtu = smt_util.SMTutil(self.c.hash_function, self.c.hash_depth)
        self.smts = [SMT(self.c.hash_function, self.c.hash_depth) for _ in range(self.c.no_smt_parts)]
        self.prime_root = None  # tuple: prime_hash, parities

    def initialize(self):
        # passive nodes
        # if old passive smts file doesn't exist create it
        if not path.exists(self.c.smt_setup_file):
            for i in tqdm(range(self.c.passive_nodes)):
                # get cert (hash)
                cert = self.c.hash_function(str(10000000000 + i))
                # insert to respective SMT
                part = i % self.c.no_smt_parts
                self.smts[part].add_node(cert)
            # save to file
            file = open(self.c.smt_setup_file, 'wb', pickle.HIGHEST_PROTOCOL)
            pickle.dump(self.smts, file)
        else:
            # load from file
            file = open(self.c.smt_setup_file, 'rb')
            basic_smts = pickle.load(file)
            self.smts = basic_smts

        # actual nodes
        for i in tqdm(range(self.c.start_no_nodes)):
            # get cert (hash)
            cert = self.c.hash_function(str(i))
            # insert to respective SMT
            part = i % self.c.no_smt_parts
            self.smts[part].add_node(cert)
        self.calc_prime_root()

    def calc_prime_root(self):
        # calculate & set prime_root
        allroots = ''
        aggr_parities = ['' for _ in range(self.c.no_aggr_parities)]
        main_parities = ['' for _ in range(self.c.main_parities)]
        aggr_par_part = 0
        main_par_part = 0
        for i in range(self.c.no_smt_parts):
            allroots += self.smts[i].roothash
            # aggregated parities
            if i < self.c.no_smt_parts - self.c.main_parities:
                aggr_parities[aggr_par_part] = hashf.from_int(hashf.get_int(aggr_parities[aggr_par_part])
                                                              ^ hashf.get_int(
                    self.smts[i].roothash[-(self.c.parity_length_bytes * 2):]),
                                                              self.c.parity_length_bytes)
                if (i + 1) % self.c.aggregated_parities == 0:
                    aggr_par_part += 1
            # main parities
            else:
                main_parities[main_par_part] = self.smts[i].roothash[-(self.c.parity_length_bytes * 2):]
                main_par_part += 1
        prime_hash = self.smtu.hash_function(allroots)
        self.prime_root = (prime_hash, aggr_parities, main_parities)

    def get_smt_roots(self):
        smt_roots = []
        for s in self.smts:
            smt_roots.append(s.roothash)
        return smt_roots

    def get_prime(self):
        return self.prime_root

    def get_a_smt_root(self, smt_part):
        return self.smts[smt_part].roothash

    def get_node_poi(self, node_id, part):
        cert = self.c.hash_function(str(node_id))
        poi, poi_bm = self.smts[part].path(cert)
        if self.c.sanity_checks:
            for h in poi:
                if h == '':
                    logging.error(f'Empty hash in poi of node: {node_id}, poi: {poi}')
        return poi.copy(), poi_bm

    def add_node(self, node_id, part, revoke=False):
        cert = self.c.hash_function(str(node_id))
        self.smts[part].add_node(cert, revoke)
        self.calc_prime_root()

    def get_lvl_caches(self, cache_level):
        lvl_caches = []
        for s in self.smts:
            lvl_caches.append(s.construct_lvl_cache(cache_level))
        return lvl_caches

    def reissue_nodes(self, nodes: List[Node]):
        for n in nodes:
            n.smt_part = self.c.no_smt_parts - 1  # put in latest SMT
            n.revoked = False
            self.add_node(n.node_id, n.smt_part)
        logging.info(f're-issued {len(nodes)} nodes: {[n.node_id for n in nodes]}')

    def revoke_nodes(self, nodes: List[Node]):
        for n in nodes:
            n.revoked = True
            self.add_node(n.node_id, n.smt_part, True)
        logging.info(f'revoked {len(nodes)} nodes: {[n.node_id for n in nodes]}')

    def construct_update(self, nodes: List[Node], revoke):
        update = []  # [(part, hash, poi, bm, revoked)]
        # re-issued or revoke nodes nodes
        for n in nodes:
            poi, poi_bm = self.get_node_poi(n.node_id, n.smt_part)
            update.append((n.smt_part, n.cert, poi, poi_bm, revoke))
        return update

    def get_unique_hash_count(self, update):
        unique_hashes = set()
        for u in update:
            for h in u[2]:
                unique_hashes.add(h)
        return unique_hashes

    def epoch_tree_change(self):
        tmp_smt = self.smts[0]
        # shift all smts
        for i in range(self.c.no_smt_parts - 1):
            self.smts[i] = self.smts[i + 1]
        self.smts[-1] = tmp_smt
        self.calc_prime_root()  # recalculate prime

    def get_some_lvl_caches(self, outdated_roots):
        # some_lvl_caches = (smt_part, lvl_cache)
        lvl_caches = self.get_lvl_caches(self.c.cache_level)
        some_lvl_caches = []
        for r in outdated_roots:
            some_lvl_caches.append((r, lvl_caches[r]))
        return some_lvl_caches
