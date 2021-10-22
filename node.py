import smt_util
import sim_config
import hashf
import logging
import copy


class Node:
    def __init__(self, node_id, smt_part, poi, poi_bm, smt_roots, prime_root, config):
        self.c: sim_config.SimConfig = config
        self.smtu = smt_util.SMTutil(self.c.hash_function, self.c.hash_depth)
        self.smt_roots = smt_roots
        self.prime_root = prime_root

        self.node_id = node_id
        self.cert = self.c.hash_function(str(node_id))
        self.smt_part = smt_part
        self.poi = poi
        self.poi_bm = poi_bm
        self.revoked = False
        self.outdated_poi = False
        self.outdated_prime = False
        self.lvl_cache_tried = False
        self.update_try = 0

        # for debugging failed sanity checks
        self.previous_poi = poi
        self.previous_poi_bm = poi_bm
        self.previous_update_hash = ''
        self.previous_update_poi = []
        self.previous_update_poi_bm = 0
        self.previous_update_revoked = False

    def __str__(self):
        return f'id: {self.node_id}, smt_part: {self.smt_part}, revoked: {self.revoked}, ' \
               f'outdated_prime: {self.outdated_prime}, outdated_poi: {self.outdated_poi}, ' \
               f'lvl_cache-tried: {self.lvl_cache_tried}, update_try: {self.update_try}, cert: {self.cert}'

    def set_prime_id_wrong_parts(self, prime_root):
        # if prime_root[0] != self.prime_root[0]:
        if prime_root != self.prime_root:
            wrong_aggr_par_parts = []
            wrong_main_par_parts = []
            # aggregated parities
            i = 0
            for o, n in zip(self.prime_root[1], prime_root[1]):
                if o != n:
                    wrong_aggr_par_parts.append(i)
                i += 1
            # main parities
            i = 0
            for o, n in zip(self.prime_root[2], prime_root[2]):
                if o != n:
                    wrong_main_par_parts.append(i)
                i += 1
            self.prime_root = copy.deepcopy(prime_root)
            self.outdated_prime = False
            return wrong_aggr_par_parts, wrong_main_par_parts
        else:
            return [], []

    def get_ided_smt_roots(self, wrong_aggr_par_parts, wrong_main_par_parts):
        selected_smt_roots = []
        for p in wrong_aggr_par_parts:
            for i in range(self.c.aggregated_parities):
                smt_part = p * self.c.aggregated_parities + i
                selected_smt_roots.append((smt_part, self.smt_roots[smt_part]))
        for p in wrong_main_par_parts:
            smt_part = self.c.aggregated_parities * self.c.no_aggr_parities + p
            selected_smt_roots.append((smt_part, self.smt_roots[smt_part]))
        return copy.deepcopy(selected_smt_roots)

    def set_ided_smt_roots(self, selected_smt_roots):
        for r in selected_smt_roots:
            if r[0] == self.smt_part and r[1] != self.smt_roots[r[0]]:
                self.outdated_poi = True
            self.smt_roots[r[0]] = r[1]

        # cover parity fails (parity okay but prime_hash wrong)
        calc_prime_root = self.calc_prime_root()
        # if False is returned, parities check out but not the prime_hash
        return calc_prime_root == self.prime_root

    def set_some_smt_roots(self, roots):
        # roots = [(part, root)]
        for r in roots:
            if r[0] == self.smt_part and self.smt_roots[r[0]] != r[1]:
                self.outdated_poi = True
            self.smt_roots[r[0]] = copy.deepcopy(r[1])

    def calc_prime_root(self):
        # calculate & set prime_root
        allroots = ''
        aggr_parities = ['' for _ in range(self.c.no_aggr_parities)]
        main_parities = ['' for _ in range(self.c.main_parities)]
        aggr_par_part = 0
        main_par_part = 0
        for i in range(self.c.no_smt_parts):
            allroots += self.smt_roots[i]
            # aggregated parities
            if i < self.c.no_smt_parts - self.c.main_parities:
                aggr_parities[aggr_par_part] = hashf.from_int(hashf.get_int(aggr_parities[aggr_par_part])
                                                              ^ hashf.get_int(
                    self.smt_roots[i][-(self.c.parity_length_bytes * 2):]),
                                                              self.c.parity_length_bytes)
                if (i + 1) % self.c.aggregated_parities == 0:
                    aggr_par_part += 1
            # main parities
            else:
                main_parities[main_par_part] = self.smt_roots[i][-(self.c.parity_length_bytes * 2):]
                main_par_part += 1
        prime_hash = self.smtu.hash_function(allroots)
        return prime_hash, aggr_parities, main_parities

    def try_poi_repair(self, cert, poi, poi_bm):
        # try to repair
        self.poi_bm = self.smtu.update_poi_with_poi(self.cert, self.poi, self.poi_bm, cert, poi, poi_bm)
        # check if successful, if so set flag & reset try counter (return it)
        return self.smt_roots[self.smt_part] == self.smtu.calc_path_root(self.cert, self.poi, self.poi_bm)

    def try_lvlc_repair(self, lvl_cache, cache_level):
        # try to repair
        self.smtu.update_poi_with_lvl_cache(self.cert, self.poi, lvl_cache, cache_level)
        # check if successful, if so set flag & reset try counter (return it)
        return self.smt_roots[self.smt_part] == self.smtu.calc_path_root(self.cert, self.poi, self.poi_bm)

    def process_update(self, update):
        # update = [(part, hash, poi, bm, revoked)]
        previous_set = False
        potential_change = False
        for u in update:
            if u[0] == self.smt_part:
                # if my hash simply assume it
                if u[1] == self.cert:
                    self.poi = copy.deepcopy(u[2])
                    self.poi_bm = u[3]
                    self.outdated_poi = False
                    break
                else:
                    if self.c.sanity_checks and not previous_set:
                        self.previous_update_hash = u[1]
                        self.previous_update_poi = copy.deepcopy(u[2])
                        self.previous_update_poi_bm = u[3]
                        self.previous_update_revoked = u[4]
                        self.previous_poi = copy.deepcopy(self.poi)
                        self.previous_poi_bm = self.poi_bm
                        previous_set = True
                        potential_change = True
                    self.poi_bm = self.smtu.update_poi_with_poi(self.cert, self.poi, self.poi_bm,
                                                                u[1], u[2], u[3], u[4])

        # check if update helped
        if self.outdated_poi and potential_change and self.smt_roots[self.smt_part] == \
                self.smtu.calc_path_root(self.cert, self.poi, self.poi_bm, 0, self.revoked):
            self.outdated_poi = False

        # DEBUG sanity-check:
        if self.c.sanity_checks and (not self.outdated_poi and not self.outdated_prime) and \
                self.smt_roots[self.smt_part] != \
                self.smtu.calc_path_root(self.cert, self.poi, self.poi_bm, 0, self.revoked):
            logging.error(f'UPDATE FAILED! calc prime is: {self.calc_prime_root()[0] == self.prime_root[0]}, '
                          f'hit an update: {potential_change}\n'
                          f'-> ACTUAL poi_bm: {self.poi_bm}, poi: {self.poi}\n'
                          f'-> STORED root: {self.smt_roots[self.smt_part]}\n'
                          f'-> CALCUL root: {self.smtu.calc_path_root(self.cert, self.poi, self.poi_bm, 0, self.revoked)}')
            return True
