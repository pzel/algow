.PHONY: clean erl

erl: clean
	erlc aw.erl
	dialyzer ./aw.erl --plt _build/default/rebar3_17.5_plt
	erl -pa ./ -noshell -eval 'erlang:display(aw:run())' -s erlang halt

clean:
	rm -f *.beam
