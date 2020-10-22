import csv
import copy
import gc
import time

from sim import BigNetSim
from sim_config import SimConfig

start = time.time()
# prepare csv
headerlist = ['no_nodes', 'cache_level', 'max_repair_tries', 'no_cacher_share', 'no_missing_nodes_share',
              'no_revoked_per_sub_share', 'parity_length_bytes',  # configs
              'total_revocations', 'total_n_needed_repairs', 'avg_try', 'lvlc_share_perc', 'failed_repairs_perc',
              'avg_update_size_bytes', 'nodes_sent_per_week_bytes', 'nodes_sent_repair_share_perc',
              'parity_fails_share_perc', 'avg_prune_update_size_bytes', 'total_encounters',
              'encounters_both_outdated_share_perc']  # results
with open('result.csv', 'w', newline='') as fp:
    wr = csv.writer(fp)
    wr.writerow(headerlist)

# prepare configs
dc = SimConfig()  # default config -> basis for modifications
dc.sanity_checks = False
dc.smt_setup_file = '100kMini.bns'
dc.passive_nodes = 100000
dc.start_no_nodes = 5000
dc.cache_level = 7
dc.max_repair_tries = 30
dc.parity_length_bytes = 2
dc.no_cacher_share = 0.1
dc.no_missing_nodes_share = 0.5
dc.new_issues_per_epoch_share = 0.001  # around 5% per year
dc.revoked_per_sub_epoch_share = 0.00028  # around 10% per year
dc.recalc_fields()  # some fields need to be recalculated based on above changes

runconfigs = [dc]

nodes_numbers = [7000, 10000, 20000, 30000, 50000, 70000, 100000]
for no in nodes_numbers:
    newc = copy.deepcopy(dc)
    newc.start_no_nodes = no
    newc.recalc_fields()
    runconfigs.append(newc)

# execute each config
for c in runconfigs:
    csv_data = [c.start_no_nodes, c.cache_level, c.max_repair_tries, c.no_cacher_share * 100,
                c.no_missing_nodes_share * 100, c.revoked_per_sub_epoch_share * 100, c.parity_length_bytes]
    result = BigNetSim(c).sim()
    csv_data.extend(result)
    # save each run as csv line
    with open('result.csv', 'a', newline='') as fp:
        wr = csv.writer(fp)
        wr.writerow(csv_data)
    gc.collect()

end = time.time()
hours, rem = divmod(end-start, 3600)
minutes, seconds = divmod(rem, 60)
print("BIG TEST took: {:0>2}:{:0>2}:{:05.2f}".format(int(hours), int(minutes), seconds))
