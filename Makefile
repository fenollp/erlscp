all:
	rebar3 do compile,eunit,xref

clean:
	$(if $(wildcard ebin/*.beam), rm ebin/*.beam)

ASM = $(wildcard test/deforestation*.erl test/unfold*.erl)

PA = _build/default/lib/erlscp/ebin/
ERLC = erlc -o ebin -pa $(PA)
ERL  = erl -noshell -pa $(PA) -pa ebin +A0 -boot start_clean

test: S $(patsubst test/%.erl,test_%,$(ASM))
test_%: SUPERC = $(ERLC) +to_asm +'{parse_transform, erlang_supercompiler}'
test_%: $(OBJECTS)
	$(SUPERC) test/$*.erl
	mv ebin/$*.S ebin/$*_.S
	$(ERLC) +to_asm test/$*.erl
	bash -c '[[ 0 -eq $$(git status --porcelain ebin/$*.S ebin/$*_.S | wc -l) ]]'

S: $(patsubst test/%.erl,S_%,$(ASM))
	bash -c '[[ 0 -eq $$(git status --porcelain ebin/*.S | wc -l) ]]'
S_%: test/%.erl
	$(ERLC) +to_asm test/$*.erl
	$(ERLC) test/$*.erl
	$(ERL) -eval 'R = $*:a(), R = $*:b().' -s init stop
