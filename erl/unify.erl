-module(unify).
-export([run/0]).
-compile(export_all).
-include_lib("eunit/include/eunit.hrl").
% Based on https://inst.eecs.berkeley.edu/~cs164/sp11/lectures/lecture22.pdf

run() ->
  eunit:test(?MODULE).

all_test_() ->
  [
   ?_assertEqual(true, unify(bind(empty_env(), b, c), a, b)),
   ?_assertEqual(false, begin
                         E0 = bind(empty_env(), b, {int, []}),
                         E1 = bind(E0, a, {bool, []}),
                         unify(E1, a, b) end),
   ?_assertEqual(true, begin
                         E0 = bind(empty_env(), b, {list, [c]}),
                         E1 = bind(E0, a, c),
                         unify(E1, {list, [a]}, b) end)
  ].

empty_env() -> dict:new().

unify(Env, TEA, TEB) ->
  catch(begin
          TA = binding_of(Env, TEA),
          TB = binding_of(Env, TEB),
          case TA =:= TB of true -> throw(true); _ -> cont end,
          case is_tvar(TA) of
            true -> bind(Env, TA, TB), throw(true);
            _ -> cont end,
          bind(Env, TB, TA),
          case is_tvar(TB) of
            true -> throw(true); _ -> cont end,
          case {TA,TB} of
            {{_TCons, LExprs}, {_TCons, RExprs}} ->
              zip_unify(Env, LExprs, RExprs);
            _ ->
              throw(false) end
        end).

zip_unify(Env, [L|Ls], [R|Rs]) ->
  case unify(Env, L, R) of
    true -> zip_unify(Env, Ls, Rs);
    false -> false end;
zip_unify(_, [], []) ->
  true;
zip_unify(_,_,_) ->
  false.

bind(Env, Left, Right) ->
  if (Left == Right) -> Env;
     true -> dict:append(Left, Right, Env) end.

binding_of(Env, TE) ->
  case get_binding(Env, TE) of
    {} -> TE;
    {B} -> binding_of(Env, B) end.

get_binding(Env, TE) ->
  case dict:find(TE, Env) of
    error -> {};
    {ok, Vars} -> {hd(lists:reverse(Vars))} end.

is_tvar(A) -> is_atom(A).
is_type(T) -> is_tuple(T).
