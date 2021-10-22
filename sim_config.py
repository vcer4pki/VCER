import hashf
import math


class SimConfig:
    def __init__(self):
        # for debugging, disable for increased performance
        self.sanity_checks = False

        # smt vars
        self.hash_function = hashf.miniminhash
        self.hash_depth = 32  # bits
        self.no_smt_parts = 52  # weeks/year
        self.parity_length_bytes = 2
        self.main_parities = 2
        self.aggregated_parities = 10  # how many smt-roots will be aggregated for each parity
        self.no_aggr_parities = int((self.no_smt_parts - self.main_parities) / self.aggregated_parities)
        self.no_parities = self.no_aggr_parities + self.main_parities
        self.prime_counter_size = 4  # 32 bit (UNIX timestamp)

        # simulation vars
        self.smt_setup_file = '100kMini.bns'  # stuff thats in the SMT but not actively used
        self.passive_nodes = 100000
        self.start_no_nodes = 1000
        self.new_issues_per_epoch_share = 0.01
        self.new_issues_per_epoch = math.ceil(self.start_no_nodes * self.new_issues_per_epoch_share)
        self.no_cacher_share = 0.1
        self.no_cacher = math.ceil(self.start_no_nodes * self.no_cacher_share)
        self.cache_level = 7  # 7 -> 100k; 10 -> 1M
        self.no_missing_nodes_share = 0.3
        self.no_missing_nodes = math.ceil(self.start_no_nodes * self.no_missing_nodes_share)
        self.encounters_per_node = 5
        self.max_repair_tries = 30

        # times vars -> time_step = 1 min; sub_epoch = 1 day; epoch = 1 week
        self.time_steps_per_sub_epoch = 24
        self.subs_per_epoch = 7
        self.epochs = 4  # 4 weeks
        self.total_time_steps = self.epochs * self.subs_per_epoch * self.time_steps_per_sub_epoch
        self.revoked_per_sub_epoch_share = 0.001
        self.revoked_per_sub_epoch = math.ceil(self.start_no_nodes * self.revoked_per_sub_epoch_share)
        #self.share_new_nodes_per_epoch = math.ceil(self.start_no_nodes * 0.05)

        # msg partial sizes
        self.hash_bytes = 32  # for calculation
        self.sig_size = 64
        self.msg_size_prime_root = self.hash_bytes + (self.parity_length_bytes * self.no_parities) \
                                   + self.prime_counter_size
        # (avg. poi-length + bitmap) * hash_size + parity_part
        self.msg_size_poi = (math.ceil(math.log(self.passive_nodes + self.start_no_nodes, 2) + 1) * self.hash_bytes) + 1
        self.msg_size_lvlc = 2 ** self.cache_level * self.hash_bytes
        self.msg_size_complete_lvlc = self.no_smt_parts * self.msg_size_lvlc

    def recalc_fields(self):
        self.no_aggr_parities = int((self.no_smt_parts - self.main_parities) / self.aggregated_parities)
        self.no_parities = self.no_aggr_parities + self.main_parities
        self.new_issues_per_epoch = math.ceil(self.start_no_nodes * self.new_issues_per_epoch_share)
        self.no_cacher = math.ceil(self.start_no_nodes * self.no_cacher_share)
        self.no_missing_nodes = math.ceil(self.start_no_nodes * self.no_missing_nodes_share)
        self.total_time_steps = self.epochs * self.subs_per_epoch * self.time_steps_per_sub_epoch
        self.revoked_per_sub_epoch = math.ceil(self.start_no_nodes * self.revoked_per_sub_epoch_share)
        self.msg_size_prime_root = self.hash_bytes + (self.parity_length_bytes * self.no_parities) \
                                   + self.prime_counter_size
        # (avg. poi-length + bitmap) * hash_size + parity_part
        self.msg_size_poi = (math.ceil(math.log(self.passive_nodes + self.start_no_nodes, 2) + 1) * self.hash_bytes) + 1
        self.msg_size_lvlc = 2 ** self.cache_level * self.hash_bytes
        self.msg_size_complete_lvlc = self.no_smt_parts * self.msg_size_lvlc

    # convert a smt_part to corresponding par_part
    def get_par_part(self, part):
        # main parity
        if part >= self.aggregated_parities * self.no_aggr_parities:
            return self.no_parities - (self.no_smt_parts - part)
        # aggregated parities
        else:
            return math.floor(part / self.aggregated_parities)
