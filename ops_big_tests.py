import copy
import time
import random
import pickle
import gc
import math
from tqdm import tqdm

import hashf
from test_smt import TestSMT
from smt_util import SMTutil


# reconstruct outdated local PoI with help of random neighbors
def bigtest_repair_rnd_nodes(smt_file, hf, missed_updates, overload_at, entropy, print_results=False):
    # simply randomly ask if someone can provide the necessary hash
    # simply use poi-update procedure on PoIs until we repaired ours (reached current root)
    random.seed()
    # load large tree
    file = open(smt_file, 'rb')
    smt: TestSMT = pickle.load(file)
    smtu = SMTutil(hf, smt.depth)
    file.close()
    # insert our own node
    target = hf('4')
    smt.add_node(target)
    target_path, target_path_bm = smt.path(target)
    # backup reference SMT for reloading
    smt_bak = copy.deepcopy(smt)
    smt_size = len(smt.int_sort_leaves)

    # measurements
    avg = 0
    mini = 999999999
    maxi = 0
    first_tries = 0
    first_ten = 0
    overloads = 0
    smt_total_loading = 0
    start = time.process_time()
    for _ in tqdm(range(entropy)):
        # reset SMT
        if len(smt.int_sort_leaves) > (smt_size * 2):
            tmp_start = time.process_time()
            smt = copy.deepcopy(smt_bak)
            target_path, target_path_bm = smt.path(target)
            tmp_stop = time.process_time()
            smt_total_loading += tmp_stop - tmp_start
            # free up memory
            gc.collect()

        # missed updates
        actual_root = ''
        for i in range(missed_updates):
            actual_root = None
            while actual_root is None:
                rnd = random.random()
                new_hash = hf(str(rnd))
                actual_root = smt.add_node(new_hash)

        # meet nodes
        for i in range(overload_at + 2):
            if i > overload_at:
                # repair path
                target_path, target_path_bm = smt.path(target)
                overloads += 1
                break
            leaf_int = random.choice(smt.int_sort_leaves)
            leaf_hash = hashf.from_int(leaf_int, smt.depth)
            add_path, add_path_bm = smt.path(leaf_hash)
            target_path_bm = smtu.update_poi_with_poi(target, target_path, target_path_bm,
                                                      leaf_hash, add_path, add_path_bm)
            # check root
            newroot = smtu.calc_path_root(target, target_path, target_path_bm)
            if actual_root == newroot:
                if i == 0:
                    first_tries += 1
                if i < 10:
                    first_ten += 1
                avg += i + 1
                mini = min(mini, i)
                maxi = max(maxi, i)
                break
    stop = time.process_time()
    if print_results:
        print('bigtest_repair_rnd_nodes(' + smt_file + ', ' + str(missed_updates) + ', ' + str(entropy) + ')')
        print('Avg. worked on ' + str('{0:.3g}'.format(avg / max(1, (entropy - overloads)))) +
              's try. Min: ' + str(mini) + ' Max: ' + str(maxi) +
              ' First Tries: ' + str(first_tries) + ' (' + '{0:.3g}'.format(first_tries/entropy*100) + '%)' +
              ' First 10 Tries: ' + str(first_ten) + ' (' + '{0:.3g}'.format(first_ten/entropy*100) + '%)' +
              ' Overloads: ' + str(overloads) + ' (' + '{0:.3g}'.format(overloads/entropy*100) + '%)')
        print('Total Elapsed Time: ' + str(stop - start) + 's.')
        print('Reloading SMTs took ' + str(smt_total_loading) + 's in total (' +
              '{0:.3g}'.format(smt_total_loading/(stop - start)*100) + '%).')
    else:
        results = {
            # params
            'smt_file': smt_file,
            'missed_updates': missed_updates,
            'overload_at': overload_at,
            'entropy': entropy,
            # values
            'avg_try': avg / max(1, (entropy - overloads)),
            'first_tries': first_tries / entropy * 100,
            'first_ten': first_ten / entropy * 100,
            'overloads': overloads / entropy * 100
        }
        # free memory, so waiting processes won't reserve it
        smt = None
        smt_bak = None
        gc.collect()
        return results


# check how often level-cache can successfully reconstruct a PoI
def bigtest_repair_lvl_cache(smt_file, hf, cache_level, missed_updates, entropy, print_results=False):
    random.seed()
    # load large tree
    file = open(smt_file, 'rb')
    smt: TestSMT = pickle.load(file)
    smtu = SMTutil(hf, smt.depth)
    file.close()
    # insert our own node
    target = hf('4')
    smt.add_node(target)
    target_path, target_path_bm = smt.path(target)
    # backup reference SMT for reloading
    smt_bak = copy.deepcopy(smt)
    smt_size = len(smt.int_sort_leaves)

    fails = 0
    start = time.process_time()
    for _ in tqdm(range(entropy)):
        # reset SMT
        if len(smt.int_sort_leaves) > (smt_size * 2):
            smt = copy.deepcopy(smt_bak)
            target_path, target_path_bm = smt.path(target)
            # free up memory
            gc.collect()

        # update & get root
        actual_root = ''
        for j in range(missed_updates):
            actual_root = None
            while actual_root is None:
                rnd = random.random()
                new_hash = hf(str(rnd))
                actual_root = smt.add_node(new_hash)
            # # check if faster than entire reconstruction
            # new_path, new_path_bm = smt.path(new_hash)
            # smt.update_lvl_cache_from_single(new_hash, new_path, new_path_bm, lvl_cache, cache_level)

        lvl_cache = smt.construct_lvl_cache(cache_level)

        # reconstruct for target
        smtu.update_poi_with_lvl_cache(target, target_path, lvl_cache, cache_level)

        # check if root is good
        constr_root = smtu.calc_path_root(target, target_path, target_path_bm)
        if constr_root != actual_root:
            fails += 1
            # update PoIs, otherwise all subsequent will fail
            target_path, target_path_bm = smt.path(target)

    stop = time.process_time()
    if print_results:
        print('bigtest_repair_lvl_cache(' + smt_file + ', ' + str(cache_level) + ', ' +
              str(missed_updates) + ', ' + str(entropy) + ')')
        print('Failed ' + str(fails) + ' times (' + '{0:.3g}'.format(fails/entropy*100) + '%).')
        print('Total Elapsed Time: ' + str(stop - start) + 's.')
    else:
        results = {
            # params
            'smt_file': smt_file,
            'cache_level': cache_level,
            'missed_updates': missed_updates,
            'entropy': entropy,
            # values
            'success': 100 - (fails / entropy * 100)
        }
        # free memory, so waiting processes won't reserve it
        smt = None
        smt_bak = None
        gc.collect()
        return results


# try to construct a complete level-cache with random PoIs
def bigtest_construct_rnd_lvl_cache(smt_file, hf, cache_level, overload_at, entropy, print_results=False):
    random.seed()
    # load large tree
    file = open(smt_file, 'rb')
    smt: TestSMT = pickle.load(file)
    smtu = SMTutil(hf, smt.depth)
    file.close()
    # evaluation cache
    target_cache_size = 2 ** cache_level

    # measurements
    avg = 0
    avg50 = 0
    avg50o = 0
    avg75 = 0
    avg75o = 0
    avg90 = 0
    avg90o = 0
    avg95 = 0
    avg95o = 0
    mini = 999999999
    maxi = 0
    overloads = 0
    start = time.process_time()
    for _ in tqdm(range(entropy)):
        new_lvl_cache = [None] * target_cache_size
        avg50b = True
        avg75b = True
        avg90b = True
        avg95b = True
        # meet nodes
        for i in range(overload_at + 2):
            if i > overload_at:  # check all overloads
                overloads += 1
                if avg50b:
                    avg50o += 1
                if avg75b:
                    avg75o += 1
                if avg90b:
                    avg90o += 1
                if avg95b:
                    avg95o += 1
                break

            leaf_int = random.choice(smt.int_sort_leaves)
            leaf_hash = hashf.from_int(leaf_int, smt.depth)
            add_path, add_path_bm = smt.path(leaf_hash)
            smtu.update_lvl_cache_with_poi(leaf_hash, add_path, add_path_bm, new_lvl_cache, cache_level)

            # check for (partial) construction of level-cache
            no_of_elements = sum(x is not None for x in new_lvl_cache)
            if avg50b and no_of_elements >= math.ceil(target_cache_size/2):  # 50%
                avg50 += i + 1
                avg50b = False
            elif avg75b and no_of_elements >= math.ceil(target_cache_size/4*3):  # 75%
                avg75 += i + 1
                avg75b = False
            elif avg90b and no_of_elements >= math.ceil(target_cache_size/10*9):  # 90%
                avg90 += i + 1
                avg90b = False
            elif avg95b and no_of_elements >= math.ceil(target_cache_size/20*19):  # 95%
                avg95 += i + 1
                avg95b = False
            elif no_of_elements == target_cache_size:
                avg += i + 1
                mini = min(mini, i)
                maxi = max(maxi, i)
                break

    stop = time.process_time()
    if print_results:
        print('bigtest_construct_rnd_lvl_cache(' + smt_file + ', ' + str(cache_level) + ', ' + str(entropy) + ')')
        print('Avg. worked on ' + str('{0:.3g}'.format(avg / max(1, (entropy - overloads)))) + 's try. Min: ' + str(mini) +
              ' Max: ' + str(maxi) + ' Overloads: ' + str(overloads))
        print('Total Elapsed Time: ' + str(stop - start) + 's.')
    else:
        results = {
            # params
            'smt_file': smt_file,
            'cache_level': cache_level,
            'overload_at': overload_at,
            'entropy': entropy,
            # values
            'avg_try': avg / max(1, (entropy - overloads)),
            'avg50': avg50 / max(1, (entropy - avg50o)),
            'avg75': avg75 / max(1, (entropy - avg75o)),
            'avg90': avg90 / max(1, (entropy - avg90o)),
            'avg95': avg95 / max(1, (entropy - avg95o)),
            'overloads': overloads / entropy * 100
        }
        # free memory, so waiting processes won't reserve it
        smt = None
        smt_bak = None
        gc.collect()
        return results


# try to repair PoI with random sub-tree-caches
def bigtest_repair_sub_cache(smt_file, hf, sub_depth, poi_depth, missed_updates, overload_at, entropy,
                             print_results=False):
    random.seed()
    # load large tree
    file = open(smt_file, 'rb')
    smt: TestSMT = pickle.load(file)
    smtu = SMTutil(hf, smt.depth)
    file.close()
    # insert our own node
    target = hf('4')
    smt.add_node(target)
    target_path, target_path_bm = smt.path(target)
    # backup reference SMT for reloading
    smt_bak = copy.deepcopy(smt)
    smt_size = len(smt.int_sort_leaves)

    # measurements
    avg = 0
    mini = 999999999
    maxi = 0
    first_tries = 0
    first_ten = 0
    overloads = 0
    start = time.process_time()
    for _ in tqdm(range(entropy)):
        # reset SMT
        if len(smt.int_sort_leaves) > (smt_size * 2):
            smt = copy.deepcopy(smt_bak)
            target_path, target_path_bm = smt.path(target)
            # free up memory
            gc.collect()

        # update & get root
        actual_root = ''
        for i in range(missed_updates):
            actual_root = None
            while actual_root is None:
                rnd = random.random()
                new_hash = hf(str(rnd))
                actual_root = smt.add_node(new_hash)

        # meet nodes
        for i in range(overload_at + 2):
            if i > overload_at:
                # update so subsequent things work
                target_path, target_path_bm = smt.path(target)
                overloads += 1
                break

            # meet a random node
            rnd_leaf = random.choice(smt.int_sort_leaves)
            rnd_hash = hashf.from_int(rnd_leaf, smt.depth)
            rnd_path, rnd_path_bm = smt.path(rnd_hash)

            # get sub caches for rnd node
            cache_level = []
            sub_cache = []
            for c in range(poi_depth):
                # check poi lvl via path bitmap
                path_pos = 0
                poi_lvl = -1
                for j in range(smt.depth):
                    path_bit = (rnd_path_bm >> smt.depth - 1 - j) & 1
                    if path_bit:
                        # check if its the correct path element
                        if path_pos < c:
                            path_pos += 1
                            continue
                        # depth of the element
                        poi_lvl = j
                        break
                # construct poi-pos -> invert respective bit in leaf
                poi_pos = rnd_leaf ^ (1 << smt.depth - 1 - poi_lvl)

                # construct sub-cache
                cache_level.append(poi_lvl)
                sub_cache.append(smt.construct_sub_cache(poi_pos, poi_lvl, sub_depth))

            # try to repair
            for c in range(poi_depth):
                target_path_bm = smtu.update_poi_with_sub_cache(target, target_path, target_path_bm,
                                                                cache_level[c], sub_cache[c])

            # also, simply try poi repair
            target_path_bm = smtu.update_poi_with_poi(target, target_path, target_path_bm,
                                                      rnd_hash, rnd_path, rnd_path_bm)

            # check if root is good
            constr_root = smtu.calc_path_root(target, target_path, target_path_bm)
            if constr_root == actual_root:
                if i == 0:
                    first_tries += 1
                if i < 10:
                    first_ten += 1
                avg += i + 1
                mini = min(mini, i)
                maxi = max(maxi, i)
                break

    stop = time.process_time()
    if print_results:
        print('bigtest_repair_sub_cache(' + smt_file + ', ' + str(sub_depth) + ', ' + str(poi_depth) +
              ', ' + str(missed_updates) + ', ' + str(entropy) + ')')
        print('Sub-Cache is ' + str(2**sub_depth * poi_depth) + ' in size.')
        print('Avg. worked on ' + str('{0:.3g}'.format(avg / max(1, (entropy - overloads)))) +
              's try. Min: ' + str(mini) + ' Max: ' + str(maxi) +
              ' First Tries: ' + str(first_tries) + ' (' + '{0:.3g}'.format(first_tries / entropy * 100) + '%)' +
              ' First 10 Tries: ' + str(first_ten) + ' (' + '{0:.3g}'.format(first_ten / entropy * 100) + '%)' +
              ' Overloads: ' + str(overloads) + ' (' + '{0:.3g}'.format(overloads / entropy * 100) + '%)')
        print('Total Elapsed Time: ' + str(stop - start) + 's.')
    else:
        results = {
            # params
            'smt_file': smt_file,
            'sub_depth': sub_depth,
            'poi_depth': poi_depth,
            'missed_updates': missed_updates,
            'overload_at': overload_at,
            'entropy': entropy,
            # values
            'cache_size': 2**sub_depth * poi_depth,
            'avg_try': avg / max(1, (entropy - overloads)),
            'first_tries': first_tries / entropy * 100,
            'first_ten': first_ten / entropy * 100,
            'overloads': overloads / entropy * 100
        }
        # free memory, so waiting processes won't reserve it
        smt = None
        smt_bak = None
        gc.collect()
        return results


# try to repair PoI with random incremental sub-tree-caches
def bigtest_repair_sub_cache_incr(smt_file, hf, sub_depth, poi_depth, missed_updates, overload_at, entropy,
                             print_results=False):
    random.seed()
    # load large tree
    file = open(smt_file, 'rb')
    smt: TestSMT = pickle.load(file)
    smtu = SMTutil(hf, smt.depth)
    file.close()
    # insert our own node
    target = hf('4')
    smt.add_node(target)
    target_path, target_path_bm = smt.path(target)
    # backup reference SMT for reloading
    smt_bak = copy.deepcopy(smt)
    smt_size = len(smt.int_sort_leaves)

    # measurements
    avg = 0
    mini = 999999999
    maxi = 0
    first_tries = 0
    first_ten = 0
    overloads = 0
    cache_size = 0
    cache_size_set = False
    start = time.process_time()
    for x in tqdm(range(entropy)):
        # reset SMT
        if len(smt.int_sort_leaves) > (smt_size * 2):
            smt = copy.deepcopy(smt_bak)
            target_path, target_path_bm = smt.path(target)
            # free up memory
            gc.collect()

        # update & get root
        actual_root = ''
        for i in range(missed_updates):
            actual_root = None
            while actual_root is None:
                rnd = random.random()
                new_hash = hf(str(rnd))
                actual_root = smt.add_node(new_hash)

        # meet nodes
        for i in range(overload_at + 2):
            if i > overload_at:
                # update so subsequent things work
                target_path, target_path_bm = smt.path(target)
                overloads += 1
                break

            # meet a random node
            rnd_leaf = random.choice(smt.int_sort_leaves)
            rnd_hash = hashf.from_int(rnd_leaf, smt.depth)
            rnd_path, rnd_path_bm = smt.path(rnd_hash)

            # get sub caches for rnd node
            # Strategy 2: extend PoI with depth, increment poi-level
            cache_level = []
            sub_cache = []
            tmp_sub_depth = sub_depth
            for c in range(poi_depth):
                # check poi lvl via path bitmap
                path_pos = 0
                poi_lvl = -1
                for j in range(smt.depth):
                    path_bit = (rnd_path_bm >> smt.depth - 1 - j) & 1
                    if path_bit:
                        # check if its the correct path element
                        if path_pos < c:
                            path_pos += 1
                            continue
                        # depth of the element
                        poi_lvl = j
                        break
                # construct poi-pos -> invert respective bit in leaf
                poi_pos = rnd_leaf ^ (1 << smt.depth - 1 - poi_lvl)

                # construct sub-cache
                cache_level.append(poi_lvl)
                sub_sub_cache = smt.construct_sub_cache(poi_pos, poi_lvl, tmp_sub_depth)
                sub_cache.append(sub_sub_cache)
                tmp_sub_depth += 1
                if not cache_size_set:
                    cache_size += 2 ** tmp_sub_depth
                    cache_size_set = True

            # try to repair
            for c in range(poi_depth):
                target_path_bm = smtu.update_poi_with_sub_cache(target, target_path, target_path_bm,
                                                                cache_level[c], sub_cache[c])

            # also, simply try poi repair
            target_path_bm = smtu.update_poi_with_poi(target, target_path, target_path_bm,
                                                      rnd_hash, rnd_path, rnd_path_bm)

            # check if root is good
            constr_root = smtu.calc_path_root(target, target_path, target_path_bm)
            if constr_root == actual_root:
                if i == 0:
                    first_tries += 1
                if i < 10:
                    first_ten += 1
                avg += i + 1
                mini = min(mini, i)
                maxi = max(maxi, i)
                break

    stop = time.process_time()
    if print_results:
        print('bigtest_repair_sub_cache_incr(' + smt_file + ', ' + str(sub_depth) + ', ' + str(poi_depth) +
              ', ' + str(missed_updates) + ', ' + str(entropy) + ')')
        print('Sub-Cache is ' + str(cache_size) + ' in size.')
        print('Avg. worked on ' + str('{0:.3g}'.format(avg / max(1, (entropy - overloads)))) +
              's try. Min: ' + str(mini) + ' Max: ' + str(maxi) +
              ' First Tries: ' + str(first_tries) + ' (' + '{0:.3g}'.format(first_tries / entropy * 100) + '%)' +
              ' First 10 Tries: ' + str(first_ten) + ' (' + '{0:.3g}'.format(first_ten / entropy * 100) + '%)' +
              ' Overloads: ' + str(overloads) + ' (' + '{0:.3g}'.format(overloads / entropy * 100) + '%)')
        print('Total Elapsed Time: ' + str(stop - start) + 's.')
    else:
        results = {
            # params
            'smt_file': smt_file,
            'sub_depth': sub_depth,
            'poi_depth': poi_depth,
            'missed_updates': missed_updates,
            'overload_at': overload_at,
            'entropy': entropy,
            # values
            'cache_size': 2**sub_depth * poi_depth,
            'avg_try': avg / max(1, (entropy - overloads)),
            'first_tries': first_tries / entropy * 100,
            'first_ten': first_ten / entropy * 100,
            'overloads': overloads / entropy * 100
        }
        # free memory, so waiting processes won't reserve it
        smt = None
        smt_bak = None
        gc.collect()
        return results


# try to repair PoI with random sub-tree-caches & additional level-cache
def bigtest_repair_mix_cache(smt_file, hf, cache_level, sub_depth, poi_depth, missed_updates, overload_at, entropy,
                             print_results=False):
    random.seed()
    # load large tree
    file = open(smt_file, 'rb')
    smt: TestSMT = pickle.load(file)
    smtu = SMTutil(hf, smt.depth)
    file.close()
    # insert our own node
    target = hf('4')
    smt.add_node(target)
    target_path, target_path_bm = smt.path(target)
    # backup reference SMT for reloading
    smt_bak = copy.deepcopy(smt)
    smt_size = len(smt.int_sort_leaves)

    avg = 0
    mini = 999999999
    maxi = 0
    first_tries = 0
    first_ten = 0
    overloads = 0
    start = time.process_time()
    for _ in tqdm(range(entropy)):
        # reset SMT
        if len(smt.int_sort_leaves) > (smt_size * 2):
            smt = copy.deepcopy(smt_bak)
            target_path, target_path_bm = smt.path(target)
            # free up memory
            gc.collect()

        # update & get root
        for i in range(missed_updates):
            actual_root = None
            while actual_root is None:
                rnd = random.random()
                new_hash = hf(str(rnd))
                actual_root = smt.add_node(new_hash)

        # lvl-cache
        lvl_cache = smt.construct_lvl_cache(cache_level)
        smtu.update_poi_with_lvl_cache(target, target_path, lvl_cache, cache_level)
        # check if root is good
        constr_root = smtu.calc_path_root(target, target_path, target_path_bm)
        if constr_root == actual_root:
            first_tries += 1
            first_ten += 1
            avg += 1
            continue

        # meet nodes
        for i in range(overload_at + 2):
            if i > overload_at:
                # update so subsequent things work
                target_path, target_path_bm = smt.path(target)
                overloads += 1
                break

            # meet a random node
            rnd_leaf = random.choice(smt.int_sort_leaves)
            rnd_hash = hashf.from_int(rnd_leaf, smt.depth)
            rnd_path, rnd_path_bm = smt.path(rnd_hash)

            # get sub caches for rnd node, *after* lvl-cache
            cache_at_level = []
            sub_cache = []
            for c in range(poi_depth):
                # check poi lvl via path bitmap
                path_pos = 0
                poi_lvl = -1
                for j in range(smt.depth):
                    # skip parts covered by lvl-cache -> can be moved to loop
                    if j < cache_level - sub_depth + 1:
                        continue
                    path_bit = (rnd_path_bm >> smt.depth - 1 - j) & 1
                    if path_bit:
                        # check if its the correct path element
                        if path_pos < c:
                            path_pos += 1
                            continue
                        # depth of the element
                        poi_lvl = j
                        break
                # construct poi-pos -> invert respective bit in leaf
                poi_pos = rnd_leaf ^ (1 << smt.depth - 1 - poi_lvl)

                # construct sub-cache
                cache_at_level.append(poi_lvl)
                sub_cache.append(smt.construct_sub_cache(poi_pos, poi_lvl, sub_depth))
                # sub_cache.append(smt.construct_sub_cache(rnd_leaf, poi_lvl, sub_depth))

            # try to repair
            for c in range(poi_depth):
                target_path_bm = smtu.update_poi_with_sub_cache(target, target_path, target_path_bm,
                                                                cache_at_level[c], sub_cache[c])
            # also, simply try poi repair
            target_path_bm = smtu.update_poi_with_poi(target, target_path, target_path_bm,
                                                      rnd_hash, rnd_path, rnd_path_bm)

            # check if root is good
            constr_root = smtu.calc_path_root(target, target_path, target_path_bm)
            if constr_root == actual_root:
                if i == 0:
                    first_tries += 1
                if i < 10:
                    first_ten += 1
                avg += i + 1
                mini = min(mini, i)
                maxi = max(maxi, i)
                break

    stop = time.process_time()
    if print_results:
        print('bigtest_repair_mix_cache(' + smt_file + ', ' + str(cache_level) + ', ' + str(sub_depth) +
              ', ' + str(poi_depth) + ', ' + str(missed_updates) + ', ' + str(entropy) + ')')
        print('Mix-Cache is ' + str(2**cache_level + 2**sub_depth * poi_depth) + ' in size.')
        print('Avg. worked on ' + str('{0:.3g}'.format(avg / max(1, (entropy - overloads)))) +
              's try. Min: ' + str(mini) + ' Max: ' + str(maxi) +
              ' First Tries: ' + str(first_tries) + ' (' + '{0:.3g}'.format(first_tries / entropy * 100) + '%)' +
              ' First 10 Tries: ' + str(first_ten) + ' (' + '{0:.3g}'.format(first_ten / entropy * 100) + '%)' +
              ' Overloads: ' + str(overloads) + ' (' + '{0:.3g}'.format(overloads / entropy * 100) + '%)')
        print('Total Elapsed Time: ' + str(stop - start) + 's.')
    else:
        results = {
            # params
            'smt_file': smt_file,
            'cache_level': cache_level,
            'sub_depth': sub_depth,
            'poi_depth': poi_depth,
            'missed_updates': missed_updates,
            'overload_at': overload_at,
            'entropy': entropy,
            # values
            'cache_size': 2**cache_level + 2**sub_depth * poi_depth,
            'avg_try': avg / max(1, (entropy - overloads)),
            'first_tries': first_tries / entropy * 100,
            'first_ten': first_ten / entropy * 100,
            'overloads': overloads / entropy * 100
        }
        # free memory, so waiting processes won't reserve it
        smt = None
        smt_bak = None
        gc.collect()
        return results


# try to repair PoI with random incremental sub-tree-caches & additional level-cache
def bigtest_repair_mix_cache_incr(smt_file, hf, cache_level, sub_depth, poi_depth, missed_updates, overload_at, entropy,
                             print_results=False):
    random.seed()
    # load large tree
    file = open(smt_file, 'rb')
    smt: TestSMT = pickle.load(file)
    smtu = SMTutil(hf, smt.depth)
    file.close()
    # insert our own node
    target = hf('4')
    smt.add_node(target)
    target_path, target_path_bm = smt.path(target)
    # backup reference SMT for reloading
    smt_bak = copy.deepcopy(smt)
    smt_size = len(smt.int_sort_leaves)

    # measurements
    avg = 0
    mini = 999999999
    maxi = 0
    first_tries = 0
    first_ten = 0
    overloads = 0
    cache_size = 0
    cache_size_set = False
    start = time.process_time()
    for x in tqdm(range(entropy)):
        # reset SMT
        if len(smt.int_sort_leaves) > (smt_size * 2):
            smt = copy.deepcopy(smt_bak)
            target_path, target_path_bm = smt.path(target)
            # free up memory
            gc.collect()

        # update & get root
        actual_root = ''
        for i in range(missed_updates):
            actual_root = None
            while actual_root is None:
                rnd = random.random()
                new_hash = hf(str(rnd))
                actual_root = smt.add_node(new_hash)

        # lvl-cache
        lvl_cache = smt.construct_lvl_cache(cache_level)
        smtu.update_poi_with_lvl_cache(target, target_path, lvl_cache, cache_level)
        # check if root is good
        constr_root = smtu.calc_path_root(target, target_path, target_path_bm)
        if constr_root == actual_root:
            first_tries += 1
            first_ten += 1
            avg += 1
            if x > 0:
                continue

        # meet nodes
        for i in range(overload_at + 2):
            if i > overload_at:
                # update so subsequent things work
                target_path, target_path_bm = smt.path(target)
                overloads += 1
                break

            # meet a random node
            rnd_leaf = random.choice(smt.int_sort_leaves)
            rnd_hash = hashf.from_int(rnd_leaf, smt.depth)
            rnd_path, rnd_path_bm = smt.path(rnd_hash)

            # get sub caches for rnd node, *after* lvl-cache
            cache_at_level = []
            sub_cache = []
            tmp_sub_depth = sub_depth
            for c in range(poi_depth):
                # check poi lvl via path bitmap
                path_pos = 0
                poi_lvl = -1
                for j in range(smt.depth):
                    # skip parts covered by lvl-cache -> can be moved to loop
                    if j < cache_level - sub_depth + 1:
                        continue
                    path_bit = (rnd_path_bm >> smt.depth - 1 - j) & 1
                    if path_bit:
                        # check if its the correct path element
                        if path_pos < c:
                            path_pos += 1
                            continue
                        # depth of the element
                        poi_lvl = j
                        break
                # construct poi-pos -> invert respective bit in leaf
                poi_pos = rnd_leaf ^ (1 << smt.depth - 1 - poi_lvl)

                # construct sub-cache
                cache_at_level.append(poi_lvl)
                sub_sub_cache = smt.construct_sub_cache(poi_pos, poi_lvl, tmp_sub_depth)
                sub_cache.append(sub_sub_cache)
                tmp_sub_depth += 1
                if not cache_size_set:
                    cache_size += 2**tmp_sub_depth
                    cache_size_set = True

            # try to repair
            for c in range(poi_depth):
                target_path_bm = smtu.update_poi_with_sub_cache(target, target_path, target_path_bm,
                                                                cache_at_level[c], sub_cache[c])
            # also, simply try poi repair
            target_path_bm = smtu.update_poi_with_poi(target, target_path, target_path_bm,
                                                      rnd_hash, rnd_path, rnd_path_bm)

            # check if root is good
            constr_root = smtu.calc_path_root(target, target_path, target_path_bm)
            if constr_root == actual_root:
                if i == 0:
                    first_tries += 1
                if i < 10:
                    first_ten += 1
                avg += i + 1
                mini = min(mini, i)
                maxi = max(maxi, i)
                break

    stop = time.process_time()
    if print_results:
        print('bigtest_repair_mix_cache_incr(' + smt_file + ', ' + str(cache_level) + ', ' + str(sub_depth) +
              ', ' + str(poi_depth) + ', ' + str(missed_updates) + ', ' + str(entropy) + ')')
        print('Mix-Cache is ' + str(2**cache_level + cache_size) + ' in size.')
        print('Avg. worked on ' + str('{0:.3g}'.format(avg / max(1, (entropy - overloads)))) +
              's try. Min: ' + str(mini) + ' Max: ' + str(maxi) +
              ' First Tries: ' + str(first_tries) + ' (' + '{0:.3g}'.format(first_tries / entropy * 100) + '%)' +
              ' First 10 Tries: ' + str(first_ten) + ' (' + '{0:.3g}'.format(first_ten / entropy * 100) + '%)' +
              ' Overloads: ' + str(overloads) + ' (' + '{0:.3g}'.format(overloads / entropy * 100) + '%)')
        print('Total Elapsed Time: ' + str(stop - start) + 's.')
    else:
        results = {
            # params
            'smt_file': smt_file,
            'cache_level': cache_level,
            'sub_depth': sub_depth,
            'poi_depth': poi_depth,
            'missed_updates': missed_updates,
            'overload_at': overload_at,
            'entropy': entropy,
            # values
            'cache_size': 2**cache_level + 2**sub_depth * poi_depth,
            'avg_try': avg / max(1, (entropy - overloads)),
            'first_tries': first_tries / entropy * 100,
            'first_ten': first_ten / entropy * 100,
            'overloads': overloads / entropy * 100
        }
        # free memory, so waiting processes won't reserve it
        smt = None
        smt_bak = None
        gc.collect()
        return results


# merge update PoIs & add level-cache to see how much they can be reduced
def bigtest_merge_poi_savings(smt_file, hf, poi_updates, cache_level, entropy, print_results=False):
    random.seed()
    # load large tree
    file = open(smt_file, 'rb')
    smt: TestSMT = pickle.load(file)
    smtu = SMTutil(hf, smt.depth)
    file.close()

    # measurements
    avg_complete_size = 0
    avg_merge_size = 0
    start = time.process_time()
    for _ in tqdm(range(entropy)):
        all_pois = []
        # collect updates
        for _ in range(poi_updates):
            # a random node
            leaf_int = random.choice(smt.int_sort_leaves)
            leaf_hash = hashf.from_int(leaf_int, smt.depth)
            add_path, add_path_bm = smt.path(leaf_hash)
            all_pois.append(add_path)

        # count all hashes and only unique ones
        complete_size = 0
        unique_hashes = set()
        for poi in all_pois:
            complete_size += len(poi) - cache_level
            if cache_level == 0:  # [:-0] doesn't work, so special case needed
                for h in poi:
                    unique_hashes.add(h)
            else:
                for h in poi[:-cache_level]:
                    unique_hashes.add(h)
        merge_size = len(unique_hashes)

        # add to results
        avg_complete_size += (poi_updates * 2) + complete_size  # first add leaves + bitmaps
        avg_merge_size += (poi_updates * 2) + merge_size

    stop = time.process_time()
    cache_size = 2 ** cache_level
    if print_results:
        print('bigtest_merge_poi_savings(' + smt_file + ', ' + str(poi_updates) +
              ', ' + str(cache_level) + ', ' + str(entropy) + ')')
        print('Avg. amount of hashes: ' + str('{0:.3g}'.format(avg_complete_size / entropy)) +
              '; avg. after merge: ' + str('{0:.3g}'.format(avg_merge_size / entropy)) +
              ' (' + str('{0:.3g}'.format(avg_merge_size / avg_complete_size * 100)) + '%)')
        print('Update size: ' + str('{0:.3g}'.format( (avg_complete_size / entropy + cache_size) * 32 / 1024)) +
              'kb; with merge: ' + str('{0:.3g}'.format( (avg_merge_size / entropy + cache_size) * 32 / 1024)) + 'kb.')
        print('Total Elapsed Time: ' + str(stop - start) + 's.')


# new strategy to merge update PoIs -> doesn't work!
def bigtest_new_poi_savings(smt_file, hf, poi_updates, entropy, print_results=False):
    random.seed()
    # load large tree
    file = open(smt_file, 'rb')
    smt: TestSMT = pickle.load(file)
    smtu = SMTutil(hf, smt.depth)
    file.close()

    # measurements
    avg_complete_size = 0
    avg_merge_size = 0
    avg_update_size = 0
    start = time.process_time()
    for _ in tqdm(range(entropy)):
        unique_old_hashes = set()
        unique_update_hashes = set()
        unique_hashes = set()
        complete_size = 0
        # collect updates
        for i in range(poi_updates):
            # add random node
            old_pois = []
            new_pois = []
            actual_root = None
            while actual_root is None:
                rnd = random.random()
                new_hash = hf(str(rnd))
                old_path, path_bm = smt.path(new_hash)
                # add it
                actual_root = smt.add_node(new_hash)
                if actual_root is not None:
                    # get all old path elements for comparison
                    for h in old_path:
                        unique_old_hashes.add(h)
                    # check new hashes
                    new_path, path_bm = smt.path(new_hash)
                    complete_size += len(new_path)
                    for h in new_path:
                        unique_hashes.add(h)
                        if h not in unique_old_hashes:
                            unique_update_hashes.add(h)
        merge_size = len(unique_hashes)
        only_new_size = len(unique_update_hashes)

        # add to results
        avg_complete_size += (poi_updates * 2) + complete_size
        avg_merge_size += (poi_updates * 2) + merge_size
        avg_update_size += (poi_updates * 2) + only_new_size

    stop = time.process_time()
    if print_results:
        print('bigtest_new_poi_savings(' + smt_file + ', ' + str(poi_updates) +
              ', ' + str(entropy) + ')')
        print('Avg. amount of hashes: ' + str('{0:.3g}'.format(avg_complete_size / entropy)) +
              '; avg. after merge: ' + str('{0:.3g}'.format(avg_merge_size / entropy)) +
              ' (' + str('{0:.3g}'.format(avg_merge_size / avg_complete_size * 100)) + '%)' +
              '; avg. only new hashes: ' + str('{0:.3g}'.format(avg_update_size / entropy)) +
              ' (' + str('{0:.3g}'.format(avg_update_size / avg_complete_size * 100)) + '%)')
        print('Update size: ' + str('{0:.3g}'.format((avg_complete_size / entropy) * 32 / 1024)) +
              'kb; with merge: ' + str('{0:.3g}'.format((avg_merge_size / entropy) * 32 / 1024)) +
              'kb; with pruning: ' + str('{0:.3g}'.format( (avg_update_size / entropy) * 32 / 1024)) + 'kb.')
        print('Total Elapsed Time: ' + str(stop - start) + 's.')
