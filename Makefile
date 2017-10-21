.PHONY: all update_erl_compile2

all:
	rebar3 do escriptize,xref,eunit,cover

clean:
	rebar3 clean
	$(if $(wildcard ebin/*.beam), rm ebin/*.beam)

update_erl_compile2: URL = 'https://raw.githubusercontent.com/erlang/otp/master/lib/stdlib/src/erl_compile.erl'
update_erl_compile2:
	curl -o src/erl_compile2.erl $(URL)
	git apply due_to_arity_0.patch

ASM = $(wildcard test/deforestation*.erl test/unfold*.erl test/try*.erl test/map*.erl)

PA = _build/default/lib/erlscp/ebin/
ERLC = erlc -o ebin -pa ebin -pa $(PA)
ERL  = erl -noshell -pa ebin +A0 -boot start_clean

src/otp_flags.hrl:
	$(ERL) -eval 'OTP = list_to_integer(case erlang:system_info(otp_release) of "R"++[A,B|_] -> [A,B]; AB -> AB end), io:format("-define(OTP_~p, true).\n", [OTP]), lists:foreach(fun (R) -> io:format("-define(OTP_~p_AND_ABOVE).\n", [R]) end, lists:seq(15, OTP)).' -s init stop >$@

old: ebin $(patsubst src/%.erl,ebin/%.beam,$(wildcard src/*.erl)) $(wildcard src/*.hrl) Makefile
ebin:
	mkdir $@
ebin/%.beam: src/%.erl
	erlc -pa ebin -o ebin -DLOG $?
test-old: $(patsubst test/%.erl,test.%,$(ASM))
test.%: old
	erlc -pa ebin -o ebin +'{parse_transform, erlang_supercompiler}' test/$*.erl
	$(ERL) -eval 'R = $*:a(), R = $*:b().' -s init stop

test: S $(patsubst test/%.erl,test_%,$(ASM))
test_%: SUPERC = $(ERLC) +'{parse_transform, erlang_supercompiler}'
test_%: $(OBJECTS)
	$(SUPERC) +to_asm test/$*.erl
	mv ebin/$*.S ebin/$*_.S
	$(ERLC) +to_asm test/$*.erl
	git add -A -f ebin/$*.S ebin/$*_.S
	git --no-pager diff --cached -- ebin
	$(SUPERC) test/$*.erl
	$(ERL) -eval 'R = $*:a(), R = $*:b().' -s init stop
	bash -c '[[ 0 -eq $$(git status --porcelain ebin/$*.S ebin/$*_.S | wc -l) ]]'

S: $(patsubst test/%.erl,S_%,$(ASM))
	git --no-pager diff -- ebin
	bash -c '[[ 0 -eq $$(git status --porcelain ebin/*.S | wc -l) ]]'
S_%: test/%.erl
	erlc -o ebin +to_asm test/$*.erl
	erlc -o ebin test/$*.erl
	$(ERL) -eval 'R = $*:a(), R = $*:b().' -s init stop
