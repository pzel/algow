-module(unify).
-export([run/0]).
-compile(export_all).
-include_lib("eunit/include/eunit.hrl").
% Based on https://inst.eecs.berkeley.edu/~cs164/sp11/lectures/lecture22.pdf

run() ->
  eunit:test(?MODULE).

all_test_() ->
  [
   ?_assertMatch({_,true},
                 pp_unify(bind(empty_env(), b, c), a, b)),

   ?_assertMatch({_,false},
                 begin
                   E0 = bind(empty_env(), b, {int, []}),
                   E1 = bind(E0, a, {bool, []}),
                   pp_unify(E1, a, b) end),

   ?_assertMatch({_,true},
                 begin
                   E0 = bind(empty_env(), b, {list, [c]}),
                   E1 = bind(E0, a, c),
                   pp_unify(E1, {list, [a]}, b) end),

   ?_assertMatch({_,true},
                 begin
                   E0 = bind(empty_env(), b, {pair, [b, a]}),
                   pp_unify(E0, a, b) end),

   %% Unification IV: Another Recursive Type
   ?_assertMatch({_, true},
                 begin
                   E0 = bind(empty_env(), b, {pair, [b,a]}),
                   E1 = bind(E0, d, {pair, [d, {pair, [d,c]}]}),
                   pp_unify(E1, a, c) end)
  ].

empty_env() -> dict:new().

pp_unify(Env, TEA, TEB) ->
  {FinalEnv, Val} = unify(Env, TEA, TEB),
  {dict:to_list(FinalEnv), Val}.

unify(Env, TEA, TEB) ->
  case (catch(do_unify(Env, TEA, TEB))) of
    {Env1, Val} -> {Env1, Val};
    E -> error({runtime_error, E}) end.

do_unify(Env, TEA, TEB) ->
  TA = binding_of(Env, TEA),
  TB = binding_of(Env, TEB),
  case TA =:= TB of true -> return(Env, true); _ -> cont end,
  case is_tvar(TA) of
    true -> return(bind(Env, TA, TB), true);
    _ -> cont end,
  E1 = bind(Env, TB, TA),
  case is_tvar(TB) of
    true -> return(E1,true); _ -> cont end,
  case {TA,TB} of
    {{_TCons, LExprs}, {_TCons, RExprs}} ->
      return(zip_unify(E1, LExprs, RExprs));
    _ ->
      return(E1,false) end.

return({Env, Val}) -> throw({Env, Val}).
return(Env, Val) -> throw({Env, Val}).

zip_unify(Env, [L|Ls], [R|Rs]) ->
  case unify(Env, L, R) of
    {E1, true} -> zip_unify(E1, Ls, Rs);
    Other -> Other end;
zip_unify(Env, [], []) ->
  {Env, true};
zip_unify(Env,_,_) ->
  {Env, false}.

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
