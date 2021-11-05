UCL_SOURCE=common.ucl tap.ucl
COMMON_SOURCE=./common-types.ucl
CACHE_SOURCE=./abstract-cache.ucl
AP_SOURCE=./ap-types.ucl
CPU_SOURCES=$(COMMON_SOURCE) $(CACHE_SOURCE) $(AP_SOURCE) ./abstract-cpu.ucl
TAP_SOURCES=$(CPU_SOURCES) ./tap-mod.ucl 
MEASURE=./measure.ucl

tap:
	uclid -s "z3 -in" --main tap $(TAP_SOURCES)
cpu:
	uclid -s "z3 -in" --main abstract_cpu $(CPU_SOURCES)
measure:
	uclid -s "z3 -in" --main measure $(TAP_SOURCES) $(MEASURE)