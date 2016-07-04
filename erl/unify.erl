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
                 do_ti([
                        lunify(b,c),
                        lpp_unify(a,b)
                       ])),

   ?_assertMatch({_,false},
                 do_ti([
                        lunify(b, {int, []}),
                        lunify(a, {bool, []}),
                        lpp_unify(a, b)
                       ])),

   ?_assertMatch({_,true},
                 do_ti([
                        lunify(b, {list, [c]}),
                        lunify(a, c),
                        lpp_unify({list, [a]}, b)
                       ])),

   ?_assertMatch({_,true},
                 do_ti([
                        lunify(b, {pair, [b, a]}),
                        lpp_unify(a, b)
                       ])),

   %% Unification IV: Another Recursive Type
   ?_assertMatch({_, true},
                 do_ti([
                        lunify(b, {pair, [b,a]}),
                        lunify(d, {pair, [d, {pair, [d,c]}]}),
                        lpp_unify(a, c)
                       ])),

   ?_assertMatch({ [{{int, []}, [{bool, []}]}|_ ],
                   false},
                 do_ti([lunify(f, {arr, [a,b]}),
                        lunify(g, {arr, [a,c]}),
                        lunify(a, {int, []}),
                        lunify(c, {bool, []}),
                        lunify(f, g),
                        %% since f ~ g, then b ~ c : bool
                        lpp_unify(b, {int, []})
                       ]))

  ].

%% Environment book-keeping
do_ti(Stmts) when is_list(Stmts) ->
  lists:foldl(fun ti_step/2, {empty_env(), true}, Stmts).

ti_step(_Stmt, {Env, false}) -> {Env, false};
ti_step({ti_stmt,Fun}, {Env, true}) -> Fun(Env);
ti_step(V,X) -> error({runtime_error, [V,X]}).

lift(Fun, A1, A2) -> {ti_stmt, fun(Env) -> Fun(Env, A1, A2) end}.
lunify(L,R) -> lift(fun unify/3, L, R).
lpp_unify(L,R) -> lift(fun pp_unify/3, L, R).


%% Implementation

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

  case TA =:= TB of
    true -> return(Env, true);
    _ -> cont end,

  case is_tvar(TA) of
    true -> return(bind(Env, TA, TB), true);
    _ -> cont end,

  E1 = bind(Env, TB, TA), % this may produce an unsound binding

  case is_tvar(TB) of
    true -> return(E1,true);
    _ -> cont end,

  case {TA,TB} of
    {{_TCons, LExprs}, {_TCons, RExprs}} ->
      return(zip_unify(E1, LExprs, RExprs));
    _ ->  % the unsound binding will bubble up here
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
