SOURCES = $(wildcard src/*.erl)
HEADERS = $(wildcard src/*.hrl)
OBJECTS = $(SOURCES:src/%.erl=ebin/%.beam)

ERLC = erlc -o ebin -pa ebin
ERL  = erl -noshell -pa ebin +A0 -boot start_clean

all: $(OBJECTS) S

ebin/%.beam : src/%.erl $(HEADERS) Makefile
	mkdir -p ebin
	erlc -pa ebin -DTEST -o ebin/ $<

clean:
	$(if $(wildcard ebin/*.beam), rm ebin/*.beam)
	rmdir ebin

test-original:
	erl -noshell -pa ebin -eval 'eunit:test("ebin",[verbose])' -s init stop

test: $(patsubst test/%.erl,test_%,$(wildcard test/*.erl))
test_%: SUPERC = $(ERLC) +to_asm +'{parse_transform, erlang_supercompiler}'
test_%: $(OBJECTS)
	$(SUPERC) test/$*.erl
	mv ebin/$*.S ebin/$*_.S
	$(ERLC) +to_asm test/$*.erl
	bash -c '[[ 0 -eq $$(git status --porcelain ebin/$*.S ebin/$*_.S | wc -l) ]]'

S: $(patsubst test/%.erl,S_%,$(wildcard test/*.erl))
S_%: test/%.erl
	$(ERLC) +to_asm test/$*.erl
	$(ERLC) test/$*.erl
	$(ERL) -eval 'R = $*:a(), R = $*:b().' -s init stop
	bash -c '[[ 0 -eq $$(git status --porcelain ebin/$*.S ebin/$*_.S | wc -l) ]]'
