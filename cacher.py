from node import Node
import logging


class Cacher(Node):
    def __init__(self, cache_level, lvl_caches, node_id, smt_part, poi, poi_bm, smt_roots, prime_root, config):
        super().__init__(node_id, smt_part, poi, poi_bm, smt_roots, prime_root, config)
        self.cache_level = cache_level
        self.lvl_caches = lvl_caches  # level-cache per smt_part
        self.outdated_lvlc = False
        self.outdated_roots = []
        self.update_try_lvlc = 0

    def __str__(self):
        return super().__str__() + f', outdated_lvlc: {self.outdated_lvlc}'

    def get_some_lvl_caches(self, outdated_roots):
        # some_lvl_caches = (smt_part, lvl_cache)
        some_lvl_caches = []
        for r in outdated_roots:
            some_lvl_caches.append((r, self.lvl_caches[r]))
        return some_lvl_caches

    def update_some_lvl_caches(self, some_lvl_caches):
        # some_lvl_caches = (smt_part, lvl_cache)
        for c in some_lvl_caches:
            self.lvl_caches[c[0]] = c[1]

        # DEBUG sanity-check:
        if self.c.sanity_checks and not self.outdated_prime:
            for i in range(self.c.no_smt_parts):
                if self.smt_roots[i] != self.smtu.lvl_cache_helper(0, 0, self.lvl_caches[i], self.cache_level):
                    logging.error(f'REPAIR LEVEL CACHES FAILED! part: {i}')
                    return True

    # override normal nodes update method to update lvl-caches as well
    def process_update(self, update):
        # update each lvl-cache
        for u in update:
            self.smtu.update_lvl_cache_with_poi(u[1], u[2], u[3], self.lvl_caches[u[0]], self.cache_level, u[4])

        # check if level-cache is now good
        if self.outdated_lvlc and not self.outdated_prime:
            any_outdated = False
            for i in range(self.c.no_smt_parts):
                if self.smt_roots[i] != self.smtu.lvl_cache_helper(0, 0, self.lvl_caches[i], self.cache_level):
                    any_outdated = True
            self.outdated_lvlc = any_outdated

        # DEBUG sanity-check:
        if self.c.sanity_checks and not self.outdated_lvlc and not self.outdated_prime:
            for i in range(self.c.no_smt_parts):
                if self.smt_roots[i] != self.smtu.lvl_cache_helper(0, 0, self.lvl_caches[i], self.cache_level):
                    logging.error(f'UPDATING LEVEL CACHES FAILED! part: {i}\n'
                                  f'node: {self}')
                    break
        # process normal node
        return super().process_update(update)

    def set_prime_id_wrong_parts(self, prime_root):
        # check if outdated in some regard
        if prime_root != self.prime_root:
            self.outdated_lvlc = True
        return super().set_prime_id_wrong_parts(prime_root)

    def set_ided_smt_roots(self, selected_smt_roots):
        # identify outdated roots to update cache
        outdated_roots = []
        for r in selected_smt_roots:
            if r[1] != self.smt_roots[r[0]]:
                outdated_roots.append(r[0])
        self.outdated_roots = outdated_roots
        return super().set_ided_smt_roots(selected_smt_roots)
