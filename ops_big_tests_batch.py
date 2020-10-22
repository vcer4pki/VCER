import sys
import csv
import hashf
from multiprocessing import Pool
import ops_big_tests

# class to execute large simulation campaigns
# execute with, e.g., test-case 4, 20 threads, results-csv, output-file:
# nohup python3 eval.py 4 20 test4.csv > h4.out &

def main():
    if len(sys.argv) < 4:
        print('USAGE: eval.py case processes csv_file')
        quit()
    case = int(sys.argv[1])
    processes = int(sys.argv[2])
    csv_file = sys.argv[3]

    # common params
    smt_file = '100kN256.smt'
    hf = hashf.minhash
    overload_at = 100
    entropy = 10000

    # for respective case, construct parameter list
    job = None  # function pointer
    param_list = []  # list of tuples, e.g.: [(1, 1), (2, 1), (3, 1)]
    if case == 1:
        job = ops_big_tests.bigtest_repair_rnd_nodes
        missed_updates = [1, 2, 3, 5, 10, 20, 30, 50, 100, 200, 300, 500, 1000]
        for i in missed_updates:
            param_list.append((smt_file, hf, i, overload_at, entropy))
    elif case == 2:
        job = ops_big_tests.bigtest_repair_lvl_cache
        cache_level = [7, 8, 9, 10, 11, 12, 13]
        missed_updates = [1, 2, 3, 5, 10, 20, 30, 50, 100, 200, 300, 500, 1000]
        for i in cache_level:
            for j in missed_updates:
                param_list.append((smt_file, hf, i, j, entropy))
    elif case == 3:
        job = ops_big_tests.bigtest_construct_rnd_lvl_cache
        overload_at = 1000
        cache_level = [5, 6, 7, 8, 9, 10]
        for i in cache_level:
            param_list.append((smt_file, hf, i, overload_at, entropy))
    elif case == 4:
        job = ops_big_tests.bigtest_repair_sub_cache
        sub_depth = [2, 3, 4, 5, 6, 7, 8]
        poi_depth = [2, 4, 8]
        missed_updates = [1, 2, 3, 5, 10, 20, 30, 50, 100, 200, 300, 500, 1000]
        for i in sub_depth:
            for j in poi_depth:
                for k in missed_updates:
                    param_list.append((smt_file, hf, i, j, k, overload_at, entropy))
    elif case == 5:
        job = ops_big_tests.bigtest_repair_mix_cache
        # 100 updates, 1024 cache size (clvl=10)
        param_list.append((smt_file, hf, 9, 7, 4, 100, overload_at, entropy))
        param_list.append((smt_file, hf, 9, 6, 8, 100, overload_at, entropy))
        param_list.append((smt_file, hf, 8, 7, 6, 100, overload_at, entropy))
        param_list.append((smt_file, hf, 8, 6, 12, 100, overload_at, entropy))
        # 1000 updates, 8192 cache size (clvl=13)
        param_list.append((smt_file, hf, 12, 10, 4, 1000, overload_at, entropy))
        param_list.append((smt_file, hf, 12, 9, 8, 1000, overload_at, entropy))
        param_list.append((smt_file, hf, 11, 10, 6, 1000, overload_at, entropy))
        param_list.append((smt_file, hf, 11, 9, 12, 1000, overload_at, entropy))
        # 10000 updates, 65536 cache size (clvl=16)
        param_list.append((smt_file, hf, 15, 13, 4, 10000, overload_at, entropy))
        param_list.append((smt_file, hf, 12, 12, 8, 10000, overload_at, entropy))
        param_list.append((smt_file, hf, 11, 13, 6, 10000, overload_at, entropy))
        param_list.append((smt_file, hf, 11, 12, 12, 10000, overload_at, entropy))
    print('created ' + str(len(param_list)) + ' jobs.')

    # execute job-queue
    pool = Pool(processes)
    results = pool.starmap(job, param_list)  # returns list of return values (dicts), blocking

    # write results into csv
    try:
        with open(csv_file, 'w', newline='') as csvfile:
            writer = csv.DictWriter(csvfile, fieldnames=results[0].keys())
            writer.writeheader()
            for data in results:
                writer.writerow(data)
    except IOError:
        print("error while writing csv!")
        quit()


if __name__ == "__main__":
    main()
