SOURCES = $(wildcard src/*.erl)
HEADERS = $(wildcard src/*.hrl)
OBJECTS = $(SOURCES:src/%.erl=ebin/%.beam)

all: $(OBJECTS)

ebin/%.beam : src/%.erl $(HEADERS) Makefile
	mkdir -p ebin
	erlc -pa ebin -DTEST -o ebin/ $<

clean:
	$(if $(wildcard ebin/*.beam), rm ebin/*.beam)
	rmdir ebin

test-original:
	erl -noshell -pa ebin -eval 'eunit:test("ebin",[verbose])' -s init stop

test: test_deforestation0
test_%: ERLC = erlc -o ebin -pa ebin +to_asm
test_%: SUPERC = $(ERLC) +'{parse_transform, erlang_supercompiler}'
test_%: $(OBJECTS)
	$(SUPERC) test/$*.erl
	mv ebin/$*.S ebin/$*_.S
	$(ERLC) test/$*.erl
	bash -c '[[ 0 -eq $$(git status --porcelain ebin/$*.S ebin/$*_.S | wc -l) ]]'
