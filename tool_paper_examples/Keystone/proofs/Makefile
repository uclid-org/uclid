COMMON_SOURCE=./../modules/common-types.ucl
CACHE_SOURCE=./../modules/abstract-cache.ucl
AP_SOURCE=./../modules/ap-types.ucl
CPU_SOURCES=$(COMMON_SOURCE) $(CACHE_SOURCE) $(AP_SOURCE) ./../modules/abstract-cpu.ucl
TAP_SOURCES=$(CPU_SOURCES) ./../modules/tap-mod.ucl 
PROOF_SOURCES=$(TAP_SOURCES) ./proof-common.ucl
INTEGRITY_PROOF=./integrity-proof.ucl

all:
	uclid --main integrity_proof $(PROOF_SOURCES) $(INTEGRITY_PROOF)

