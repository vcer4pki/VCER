import hashf
import bisect


# this class is only needed for visualization
class NodeViz:
    def __init__(self, nhash, pos, depth, is_leaf, left=None, right=None):
        self.nhash = nhash
        self.pos = pos
        self.depth = depth
        self.is_leaf = is_leaf
        self.left = left
        self.right = right

    def set_new(self, nhash, pos, depth, is_leaf, left=None, right=None):
        self.nhash = nhash
        self.pos = pos
        self.depth = depth
        self.is_leaf = is_leaf
        self.left = left
        self.right = right
        return self

    def __str__(self):
        return 'Pos:' + str(self.pos) + '; H:' + self.nhash


# class for networking test
class Node:
    def HF(x):
        return hashf.minhash(x)

    def __init__(self, id):
        self.id = id
        self.hash = Node.HF(self.id)
        self.root = None
        self.cert = None
        self.path = None
        self.path_bm = None


# class for storing SMT with LUT & all CA operations
class TestSMT:
    def __init__(self, hash_function, depth):
        self.hash_function = hash_function
        self.depth = depth

        self.root = NodeViz(hash_function(''), 0, 0, True)  # empty tree, only needed for visualization
        self.roothash = ''  # current root hash
        self.nodes = {}  # LUT, access with get_hash() / set_hash()
        self.int_sort_leaves = []  # optional, but nice to have for big tests

    # get hash at coordinate (bits) and depth -> LUT
    def get_hash(self, pos, depth):
        # return root
        if depth == 0:
            return self.nodes.get((0, 0), '')
        elif depth == self.depth:
            return self.nodes.get((pos, depth), '')
        else:
            # normalize pos
            del_bits = 2 ** (self.depth - depth) - 1  # TODO faster method with bitshifts?
            pos = pos & ~del_bits
            return self.nodes.get((pos, depth), '')

    # set hash at coordinate (bits) and depth -> LUT
    def set_hash(self, pos, depth, val):
        # skip empty vals
        if val == '':
            return
        # return root
        if depth == 0:
            self.nodes[(0, 0)] = val
        elif depth == self.depth:
            self.nodes[(pos, depth)] = val
        else:
            # normalize pos
            del_bits = 2 ** (self.depth - depth) - 1
            pos = pos & ~del_bits
            self.nodes[(pos, depth)] = val

    # add a new value & reconstruct root
    def add_node(self, new_hash):
        # convert to bitmap
        hash_bm = hashf.get_int(new_hash)
        # check if already there
        if self.get_hash(hash_bm, self.depth) != '':
            print('Leaf already in SMT, skip...')
            return None
        # insert into LUT
        self.set_hash(hash_bm, self.depth, new_hash)
        # optional, but nice to have for some tests
        bisect.insort(self.int_sort_leaves, hash_bm)

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

    # lookup helper for sub-trees
    def set_hash_dict(self, pos, depth, val, posdict):
        # skip empty vals
        if val == '':
            return
        if depth >= self.depth:
            posdict[(pos, depth)] = val
        else:
            # normalize pos
            del_bits = 2 ** (self.depth - depth) - 1
            pos = pos & ~del_bits
            posdict[(pos, depth)] = val

    # construct one sub-tree to be part of a sub-tree-cache
    def construct_sub_cache(self, pos, start_depth, cache_depth):
        # return list of pos, depth pairs pointing to regarding hash
        # pos & depth: position of origin
        # cache_depth: how many depth-bits after pos are considered for sub_cache
        sub_cache = {}
        count = 2**cache_depth
        # delete bits up to depth
        del_bits = 2 ** (self.depth - start_depth) - 1
        sub_pos = pos & ~del_bits
        for i in range(count):
            # get regarding hash by adding i to origin at bit-pos depth
            # shift i and OR it to sub_pos
            tmp_pos = sub_pos | (i << self.depth - start_depth - cache_depth)
            # look up correct hash
            add_hash = self.get_hash(tmp_pos, (start_depth + cache_depth))
            if add_hash == '':
                continue
            # add to sub_cache
            self.set_hash_dict(tmp_pos, (start_depth + cache_depth), add_hash, sub_cache)
            # TODO remove depth info from dict -> redundant
        return sub_cache

    # recursive tree structure construction, only needed for visualization
    # call with smt.root for correct behavior
    def update_tree(self, node):
        if node is None:
            return None
        node_pos = node.pos
        node_depth = node.depth

        # reached leaf create leaf node object for it
        if node_depth >= self.depth:
            return node.set_new(self.get_hash(node_pos, node_depth), node_pos, node_depth, True)

        # update left node
        lpos = node_pos & ~(1 << (self.depth - 1 - node_depth))
        ndepth = node_depth + 1
        # check for empty path & skip if not interesting (we do not want to construct the ENTIRE tree)
        if self.get_hash(lpos, ndepth) == '':  # no hash, no node
            lnode = None
        else:
            if node.left is None:
                lnode = NodeViz(self.get_hash(lpos, ndepth), lpos, ndepth, True)
            else:
                lnode = node.left.set_new(self.get_hash(lpos, ndepth), lpos, ndepth, True)

        # update right node, same as above
        rpos = node_pos | (1 << (self.depth - 1 - node_depth))
        if self.get_hash(rpos, ndepth) == '':
            rnode = None
        else:
            if node.right is None:
                rnode = NodeViz(self.get_hash(rpos, ndepth), rpos, ndepth, True)
            else:
                rnode = node.right.set_new(self.get_hash(rpos, ndepth), rpos, ndepth, True)

        # in between node with left and right paths
        return node.set_new(self.get_hash(node_pos, node_depth), node_pos, node_depth, False,
                            self.update_tree(lnode), self.update_tree(rnode))

    # recursive helper for printing tree (called by print_tree)
    # set full=True to print entire tree without any omissions
    def strhelp(self, node, indent, prev_node_has_both, full):
        if node is None:
            return indent * '-' + '0'  # should not happen
        elif node.is_leaf:
            return indent * '-' + node.hash
        else:
            # only print in between nodes, if it's of interest (real child)
            result = ''
            node_has_both = node.left is not None and node.right is not None  # current node has 2 real children
            # if one of the children is real, we need to print something
            if full or node.left is not None or node.right is not None:
                # print current hash if it has two real children or the previous node had two
                if full or prev_node_has_both or node_has_both:
                    result = indent * '-' + node.hash + '\n'
                if full or node.left is not None:  # print left child
                    result += self.strhelp(node.left, indent + 1, node_has_both, full)
                if full or node_has_both:  # need a new line for right after left child
                    result += '\n'
                if full or node.right is not None:  # print right child
                    result += self.strhelp(node.right, indent + 1, node_has_both, full)
            return result

    def print_tree(self, full=False):
        print(self.strhelp(self.root, 0, False, full))
