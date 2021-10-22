import hashf


class SMT:
    def __init__(self, hash_function, depth):
        self.hash_function = hash_function
        self.depth = depth
        self.roothash = ''  # current root hash
        self.nodes = {}  # LUT, access with get_hash() / set_hash()

    # get hash at coordinate (bits) and depth -> LUT
    def get_hash(self, pos, depth):
        # return root
        if depth == 0:
            return self.nodes.get((0, 0), '')
        elif depth == self.depth:
            return self.nodes.get((pos, depth), '')
        else:
            # normalize pos
            del_bits = 2 ** (self.depth - depth) - 1
            pos = pos & ~del_bits
            return self.nodes.get((pos, depth), '')

    # set hash at coordinate (bits) and depth -> LUT
    def set_hash(self, pos, depth, val):
        # skip empty vals
        if val == '' and self.get_hash(pos, depth) == '':
            return
        removal = val == ''
        # return root
        if depth == 0:
            if removal:  # only applies when smt is empty!
                print('set_hash set empty smt root')
                self.nodes.pop((0, 0))
            else:
                self.nodes[(0, 0)] = val
        elif depth == self.depth:
            if removal:
                self.nodes.pop((pos, depth))
            else:
                self.nodes[(pos, depth)] = val
        else:
            # normalize pos
            del_bits = 2 ** (self.depth - depth) - 1
            pos = pos & ~del_bits
            if removal:
                self.nodes.pop((pos, depth))
            else:
                self.nodes[(pos, depth)] = val

    # add a new value & reconstruct root
    def add_node(self, new_hash, revoke=False):
        # convert to bitmap
        hash_bm = hashf.get_int(new_hash)
        # insert into LUT
        if revoke:
            self.set_hash(hash_bm, self.depth, '')
        else:
            self.set_hash(hash_bm, self.depth, new_hash)

        # update all positions by going upwards
        for i in range(self.depth):
            neighbor_bit = (hash_bm >> i) & 1
            if neighbor_bit:
                neighbor = hash_bm & ~(1 << i)
                lhash = self.get_hash(neighbor, self.depth - i)
                rhash = self.get_hash(hash_bm, self.depth - i)
            else:
                lhash = self.get_hash(hash_bm, self.depth - i)
                neighbor = hash_bm | (1 << i)
                rhash = self.get_hash(neighbor, self.depth - i)

            hashadd = hashf.hashadd(self.hash_function, lhash, rhash)  # calculate new sub-root of lvl
            self.set_hash(hash_bm, self.depth - i - 1, hashadd)
        self.roothash = self.get_hash(0, 0)  # set new root
        return self.roothash

    # construct PoI with LUT for a leaf
    def path(self, my_hash):
        path = []
        path_bm = 0
        hash_bm = hashf.get_int(my_hash)

        # go through levels of hash upwards
        for i in range(self.depth):
            # get neighbor pos
            neighbor_bit = (hash_bm >> i) & 1
            if neighbor_bit:
                neighbor = hash_bm & ~(1 << i)
            else:
                neighbor = hash_bm | (1 << i)
            neighbor_hash = self.get_hash(neighbor, self.depth - i)

            # only add relevant node, ie neighbor is a real child (no empty hashes)
            # path_bitmap is needed so its clear which level the PoI-hash belongs to
            if neighbor_hash != '':
                path_bm = path_bm | (1 << i)
                path.append(neighbor_hash)  # store hash for PoI
        return path, path_bm

    # construct level-cache with LUT
    def construct_lvl_cache(self, cache_level):
        target_cache_size = 2 ** cache_level
        ordered_cache = [None] * target_cache_size
        # just go through all no. 0 - 2**n
        for i in range(target_cache_size):
            # then bitshift depth-clvl
            pos = i << self.depth - cache_level
            # use LUT on pos to just look-up correct hash
            ordered_cache[i] = self.get_hash(pos, cache_level)
        return ordered_cache
