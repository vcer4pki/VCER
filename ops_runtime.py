from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives import hashes
import time
import secrets
import copy

import hashf
from ca import CA
from sim_config import SimConfig
from node import Node
from smt_util import SMTutil


##### setup
### ECDSA
# generate key pair
private_key = ec.generate_private_key(ec.SECP256R1(), default_backend())
public_key = private_key.public_key()

# sign a message
msg = b'TEST'
sig = private_key.sign(msg, ec.ECDSA(hashes.SHA256()))

# verify a message
try:
    public_key.verify(sig, msg, ec.ECDSA(hashes.SHA256()))
except:
    print('Could not verify signature!')
else:
    print('Signature is good!')

### SMTs
# basics
config = SimConfig()
config.hash_function = hashf.minhash
config.hash_depth = 256
config.passive_nodes = 10000
config.smt_setup_file = '10k256.bns'
config.recalc_fields()
ca = CA(config)
ca.initialize()
smtu = SMTutil(config.hash_function, config.hash_depth)


##### sig & prime check
repetitions = 10000
# construct prime message & sign
msg = secrets.token_bytes(32 + 14 + 4)  # hash + 7x2 Bytes parity + timestamp
sig = private_key.sign(msg, ec.ECDSA(hashes.SHA256()))

# main node
node_id = 1000001
smt_part = 1
ca.add_node(node_id, smt_part)
poi, poi_bm = ca.get_node_poi(node_id, smt_part)
prime_root = ca.get_prime()
smt_roots = ca.get_smt_roots()
outdated_node = Node(node_id, smt_part, poi, poi_bm, smt_roots.copy(), copy.deepcopy(prime_root), config)
# copies for repetition
outdated_nodes = []
for _ in range(repetitions):
    outdated_nodes.append(copy.deepcopy(outdated_node))

# outdate 1 main and 2 aggr
main_node_id = 1000002
main_smt_part = config.no_smt_parts - 1  # main
ca.add_node(main_node_id, main_smt_part)
aggr1_node_id = 1000003
aggr1_smt_part = 5
ca.add_node(aggr1_node_id, aggr1_smt_part)
aggr2_node_id = 1000004
aggr2_smt_part = 32
ca.add_node(aggr2_node_id, aggr2_smt_part)

prime_root = ca.get_prime()
smt_roots = ca.get_smt_roots()
main_poi, main_poi_bm = ca.get_node_poi(main_node_id, main_smt_part)
main_node = Node(main_node_id, main_smt_part, main_poi, main_poi_bm, smt_roots.copy(), copy.deepcopy(prime_root), config)
aggr1_poi, aggr1_poi_bm = ca.get_node_poi(aggr1_node_id, aggr1_smt_part)
aggr1_node = Node(aggr1_node_id, aggr1_smt_part, aggr1_poi, aggr1_poi_bm, smt_roots.copy(), copy.deepcopy(prime_root), config)
aggr2_poi, aggr2_poi_bm = ca.get_node_poi(aggr2_node_id, aggr2_smt_part)
aggr2_node = Node(aggr2_node_id, aggr2_smt_part, aggr2_poi, aggr2_poi_bm, smt_roots.copy(), copy.deepcopy(prime_root), config)

# exchange setup
wrong_aggr_par_parts, wrong_main_par_parts = outdated_node.set_prime_id_wrong_parts(main_node.prime_root)
selected_smt_roots = main_node.get_ided_smt_roots(wrong_aggr_par_parts, wrong_main_par_parts)

start = time.process_time()
for i in range(repetitions):
    public_key.verify(sig, msg, ec.ECDSA(hashes.SHA256()))
    outdated_nodes[i].set_prime_id_wrong_parts(main_node.prime_root)
    outdated_nodes[i].set_ided_smt_roots(selected_smt_roots)
stop = time.process_time()
print(f'Total for sig & prime check: {stop - start:1.2f}s, each took {(stop - start) * 1000 / repetitions:1.4f}ms')


##### PoI authentication
repetitions = 10000
node_id = 1000010
node_hash = config.hash_function(str(node_id))
smt_part = config.no_smt_parts - 1
smt_root = ca.get_a_smt_root(smt_part)
ca.add_node(node_id, smt_part)
poi, poi_bm = ca.get_node_poi(node_id, smt_part)

start = time.process_time()
for _ in range(repetitions):
    smtu.calc_path_root(node_hash, poi, poi_bm)
stop = time.process_time()
print(f'Total for PoI authentication: {stop - start:1.2f}s, each took {(stop - start) * 1000 / repetitions:1.4f}ms')


##### processing {x} PoI Updates
repetitions = 200
x = 20
# target
node_id = 1000020
node_hash = config.hash_function(str(node_id))
smt_part = config.no_smt_parts - 1
ca.add_node(node_id, smt_part)
poi, poi_bm = ca.get_node_poi(node_id, smt_part)

# copies for repetition
pois = []
pois_bm = []
for _ in range(repetitions):
    pois.append(poi.copy())
    pois_bm.append(poi_bm)

# updates
update = []
for i in range(x):
    new_node_id = 1000021 + i
    ca.add_node(new_node_id, smt_part)
for i in range(x):
    new_node_id = 1000021 + i
    new_node_hash = config.hash_function(str(new_node_id))
    new_poi, new_poi_bm = ca.get_node_poi(new_node_id, smt_part)
    update.append((new_node_hash, new_poi, new_poi_bm))

# execute
start = time.process_time()
for i in range(repetitions):
    # process updates
    for j in range(x):
        pois_bm[i] = smtu.update_poi_with_poi(node_hash, pois[i], pois_bm[i], update[j][0], update[j][1], update[j][2])
    # validate
    smtu.calc_path_root(node_hash, pois[i], pois_bm[i])
stop = time.process_time()
print(f'Total for processing {x} PoI Updates: {stop - start:1.2f}s, each took {(stop - start) * 1000 / repetitions:1.4f}ms')


##### Repair PoI with PoI
repetitions = 10000
# target
node_id = 1000030
node_hash = config.hash_function(str(node_id))
smt_part = config.no_smt_parts - 2
ca.add_node(node_id, smt_part)
poi, poi_bm = ca.get_node_poi(node_id, smt_part)

# update
new_node_id = 1000031
ca.add_node(new_node_id, smt_part)
new_node_hash = config.hash_function(str(new_node_id))
new_poi, new_poi_bm = ca.get_node_poi(new_node_id, smt_part)

# copies for repetition
pois = []
pois_bm = []
for _ in range(repetitions):
    pois.append(poi.copy())
    pois_bm.append(poi_bm)

# update
# execute
start = time.process_time()
for i in range(repetitions):
    # try repair
    pois_bm[i] = smtu.update_poi_with_poi(node_hash, pois[i], pois_bm[i], new_node_hash, new_poi, new_poi_bm)
    smtu.calc_path_root(node_hash, pois[i], pois_bm[i])
stop = time.process_time()
print(f'Total for single PoI Repair: {stop - start:1.2f}s, each took {(stop - start) * 1000 / repetitions:1.4f}ms')



##### Repair PoI with Level-Cache
repetitions = 10000
cache_level = 7
# target
node_id = 1000040
node_hash = config.hash_function(str(node_id))
smt_part = config.no_smt_parts - 2
ca.add_node(node_id, smt_part)
poi, poi_bm = ca.get_node_poi(node_id, smt_part)

# updates
update = []
for i in range(10):
    new_node_id = 1000041 + i
    ca.add_node(new_node_id, smt_part)

# cache
lvl_cache = ca.get_lvl_caches(cache_level)[smt_part]

# copies for repetition
pois = []
pois_bm = []
for _ in range(repetitions):
    pois.append(poi.copy())
    pois_bm.append(poi_bm)

# update
# execute
start = time.process_time()
for i in range(repetitions):
    # try repair
    smtu.update_poi_with_lvl_cache(node_hash, pois[i], lvl_cache, cache_level)
    smtu.calc_path_root(node_hash, pois[i], pois_bm[i])
stop = time.process_time()
print(f'Total for {cache_level}-Cache Repair: {stop - start:1.2f}s, each took {(stop - start) * 1000 / repetitions:1.4f}ms')
