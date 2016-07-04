-module(unify).
-export([run/0]).
% Based on https://inst.eecs.berkeley.edu/~cs164/sp11/lectures/lecture22.pdf

empty_env() -> dict:new().

run() ->
  E0 = bind(empty_env(), b, c),
  E1 = bind(E0, c, c),
  unify(E1, a, b).

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
              throw(all_true(zip_unify(Env, LExprs, RExprs)));
            _ -> throw(false) end
        end).

all_true(L) -> lists:all(fun(X) -> X == true end, L).

zip_unify(Env, [A,As], [B, Bs]) ->
  case unify(


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
