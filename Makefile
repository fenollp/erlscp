ERLC_FLAGS=-pa ebin -pa /tmp/erlang-15.b.1-dfsg/lib/eunit -DTEST
SOURCES=$(wildcard src/*.erl)
HEADERS=$(wildcard src/*.hrl)
OBJECTS=$(SOURCES:src/%.erl=ebin/%.beam)
all: $(OBJECTS) test
ebin/%.beam : src/%.erl $(HEADERS) Makefile
	erlc $(ERLC_FLAGS) -o ebin/ $<
clean:
	-rm $(OBJECTS)
test:
	erl -noshell -pa ebin \
	  -eval 'eunit:test("ebin",[verbose])' \
	  -s init stop
