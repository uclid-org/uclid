UCL_SOURCE=common.ucl tap.ucl
COMMON_SOURCE=./common-types.ucl
CACHE_SOURCE=./abstract-cache.ucl
AP_SOURCE=./ap-types.ucl
CPU_SOURCES=$(COMMON_SOURCE) $(CACHE_SOURCE) $(AP_SOURCE) ./abstract-cpu.ucl
TAP_SOURCES=$(CPU_SOURCES) ./tap-mod.ucl 
MEASURE=./measure.ucl

tap:
	uclid --main tap $(TAP_SOURCES)
cpu:
	uclid --main abstract_cpu $(CPU_SOURCES)
measure:
	uclid --main measure $(TAP_SOURCES) $(MEASURE)
