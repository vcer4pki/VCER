import hashf
import copy


# helper class for nodes to handle PoIs & Caches
class SMTutil:
    def __init__(self, hash_function, depth):
        self.hash_function = hash_function
        self.depth = depth

    # calc path root for PoI verification
    def calc_path_root(self, my_hash, path, path_bm, lvl=0, revoked=False):
        tmp_path = path.copy()
        hash_bm = hashf.get_int(my_hash)
        if revoked:
            result = ''
        else:
            result = my_hash

        # for all tree levels...
        for i in range(self.depth - lvl):
            # check for empty, get relevant hash
            is_not_empty = (path_bm >> i) & 1
            if is_not_empty:
                neighbor_hash = tmp_path[0]
                del tmp_path[0]
            else:
                neighbor_hash = ''

            # check if neighbor is left or right (last bit is 0/1), then add the hashes
            is_left = (hash_bm >> i) & 1
            if is_left:
                result = hashf.hashadd(self.hash_function, neighbor_hash, result)
            else:
                result = hashf.hashadd(self.hash_function, result, neighbor_hash)
        return result

    # update a PoI via a single update-PoI, returns new my_path_bm! (not updateable via params)
    def update_poi_with_poi(self, my_hash, my_path, my_path_bm, new_hash, new_path, new_path_bm, revoked=False):
        my_hash_bm = hashf.get_int(my_hash)
        new_hash_bm = hashf.get_int(new_hash)
        xor_hash = my_hash_bm ^ new_hash_bm
        and_path = my_path_bm & new_path_bm

        target_pos = -1
        # target position is left-most 1 in xor_hash
        for i in range(self.depth):
            xor_bit = (xor_hash >> self.depth - 1 - i) & 1
            if xor_bit:
                target_pos = i
                break

        # correct path position for path update is the 1 count in and_path to target position
        # check if insert or update by checking if target position is also 1 (if not it's an insert)
        path_count = 0
        is_update = False
        is_removal = False
        for i in range(self.depth):
            bit = (and_path >> self.depth - 1 - i) & 1
            if bit:
                if i < target_pos:
                    path_count += 1
                    # update all PoI elements before split -> should be same, helps with reconstruction
                    my_path[len(my_path) - path_count] = new_path[len(new_path) - path_count]
                elif i == target_pos:
                    path_count += 1
                    if len(new_path) == path_count:
                        path_count -= 1
                        is_removal = True
                    else:
                        is_update = True
                    break
                else:
                    is_update = False
                    if not (new_path_bm >> self.depth - 1 - target_pos) & 1:
                        is_removal = True
                    break
            if i == self.depth - 1:
                # not set in new path -> remove, otherwise no change
                if not (new_path_bm >> self.depth - 1 - target_pos) & 1 and \
                        (my_path_bm >> self.depth - 1 - target_pos) & 1:
                    is_removal = True
                elif (new_path_bm >> self.depth - 1 - target_pos) & 1 and \
                        not (my_path_bm >> self.depth - 1 - target_pos) & 1:
                    tmp = 0  # do nothing for insert
                else:
                    found_bit = False
                    for j in range(target_pos + 1, self.depth):
                        if (new_path_bm >> self.depth - 1 - j) & 1:
                            found_bit = True
                    if not found_bit:
                        return my_path_bm
                    elif found_bit:
                        path_count += 1
                        is_update = True

        # construct hash via new poi
        if not is_removal:
            update_hash = self.calc_path_root(new_hash, new_path, new_path_bm, (target_pos + 1), revoked)
        else:
            update_hash = None

        if is_update:
            my_path[len(my_path) - path_count] = update_hash
        else:
            if not is_removal:
                # insert new element
                my_path.insert(len(my_path) - path_count, update_hash)
                # update bitmap
                my_path_bm = my_path_bm | (1 << (self.depth - 1 - target_pos))
            else:
                # remove element
                my_path.pop(len(my_path) - path_count - 1)
                # update bitmap
                my_path_bm = my_path_bm & ~(1 << (self.depth - 1 - target_pos))

        return my_path_bm

    # update a level-cache with update a PoI
    def update_lvl_cache_with_poi(self, new_hash, new_path, new_path_bm, lvl_cache, cache_level, revoked=False):
        # need to calc own node for clvl's neighbor in path
        new_cache_hash = self.calc_path_root(new_hash, new_path, new_path_bm, cache_level, revoked)

        # check which part to replace in cache
        part_no = hashf.get_int(new_hash)
        for i in range(self.depth - cache_level):
            part_no = part_no & ~1
            part_no = part_no >> 1

        # replace
        lvl_cache[part_no] = new_cache_hash

    # update a PoI with a given level-cache
    # assumes all relevant cache level hashes are filled for all hashes (highly likely)
    def update_poi_with_lvl_cache(self, my_hash, my_path, lvl_cache, cache_level):
        # construct number from first lvl_cache-size bits of hash
        my_hash_bm = hashf.get_int(my_hash)
        part_no = my_hash_bm

        del_bits = 2 ** (self.depth - cache_level) - 1
        part_no = part_no & ~del_bits
        part_no = part_no >> (self.depth - cache_level)
        # use invert to construct required neighbor-paths
        part_no_neg = ~part_no

        # rebuild path per bit-level
        for i in range(cache_level):
            # calculate fitting hash from lvl_cache
            calc_hash = self.lvl_cache_helper(part_no_neg, i + 1, lvl_cache, cache_level)
            # replace in my PoI, should be always right (inside cache level)
            my_path[len(my_path) - 1 - i] = calc_hash
            # for next iteration return pervious bit to original part_no
            part_no_neg = part_no_neg ^ (1 << cache_level - 1 - i)

    # helper for constructing subroot of a level-cache
    # target is bitmap of targeted hash & on_lvl describes which level is of interest (eg 1 is first branch in SMT)
    def lvl_cache_helper(self, target, on_lvl, lvl_cache, cache_level):
        # as lvl_cache is ordered we simply convert bitmap for correct position
        if on_lvl >= cache_level:
            return lvl_cache[target]

        # set new targets
        targetleft = target & ~(1 << cache_level - 1 - on_lvl)
        targetright = target | (1 << cache_level - 1 - on_lvl)

        left = self.lvl_cache_helper(targetleft, on_lvl + 1, lvl_cache, cache_level)
        right = self.lvl_cache_helper(targetright, on_lvl + 1, lvl_cache, cache_level)
        return hashf.hashadd(self.hash_function, left, right)

    # lookup helper for sub-trees
    # get hash at coordinate (BitArray), also for coordinates < self.depth!
    def get_hash_dict(self, pos, depth, posdict, remove=False):
        if depth >= self.depth:
            result = posdict.get((pos, depth), '')
            if remove and result != '':
                del posdict[(pos, depth)]
            return result
        else:
            # normalize pos
            del_bits = 2 ** (self.depth - depth) - 1
            pos = pos & ~del_bits
            result = posdict.get((pos, depth), '')
            if remove and result != '':
                del posdict[(pos, depth)]
            return result

    # update a PoI with a sub-tree of a sub-tree-cache
    def update_poi_with_sub_cache(self, my_hash, my_path, my_path_bm, cache_depth, sub_cache):
        # update all path crossings found in sub_cache
        my_hash_bm = hashf.get_int(my_hash)
        # for all elements in sub_cache
        for k, v in sub_cache.items():
            # k[0] = pos; k[1] = depth
            xor_hash = my_hash_bm ^ k[0]
            target_pos = -1
            # check diff (XOR) in relevant range
            for i in range(k[1]):
                xor_bit = (xor_hash >> self.depth - 1 - i) & 1
                if xor_bit:
                    if i < cache_depth:
                        break
                    target_pos = i
                    break
            if target_pos < 0:  # not relevant for us
                continue

            # if relevant calculate up to diff_pos
            update_hash = self.sub_cache_helper(k[0], target_pos + 1, sub_cache, k[1])

            # find correct position in poi
            # check if bitmap @ target_pos is set -> is_update
            path_count = 0
            is_update = False
            for i in range(target_pos + 1):
                bit = (my_path_bm >> self.depth - 1 - i) & 1
                if bit:
                    if i < target_pos:
                        path_count += 1
                    elif i == target_pos:
                        path_count += 1
                        is_update = True
                        break

            if is_update:
                my_path[len(my_path) - path_count] = update_hash
            else:
                my_path.insert(len(my_path) - path_count, update_hash)
                # update bitmap
                my_path_bm = my_path_bm | (1 << (self.depth - target_pos - 1))
        return my_path_bm

    # helper for constructing sub-root of the sub_cache tree
    def sub_cache_helper(self, target, on_lvl, sub_cache, cache_depth):
        # similar to lvl_cache_helper
        if on_lvl >= cache_depth:
            return self.get_hash_dict(target, on_lvl, sub_cache)

        targetleft = target & ~(1 << self.depth - 1 - on_lvl)
        targetright = target | (1 << self.depth - 1 - on_lvl)
        left = self.sub_cache_helper(targetleft, on_lvl + 1, sub_cache, cache_depth)
        right = self.sub_cache_helper(targetright, on_lvl + 1, sub_cache, cache_depth)
        return hashf.hashadd(self.hash_function, left, right)
