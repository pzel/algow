-module(aw).
-compile(export_all).

-type exp() :: {evar, atom()}
             | {elit, lit()}
             | {eapp, exp(), exp()}
             | {elam, atom(), exp()}
             | {elet, atom(), exp(), exp()}
             | {eop, op(), exp(), exp()}.

-type lit() :: {lint, integer()}
             | {lbool, boolean()}.

-type op() :: op_and
            | op_or
            | op_add
            | op_mul.

-type typ() :: {tvar, atom()}
             | tint
             | tbool
             | {tfun, typ(), typ()}.

-type scheme() :: {scheme, [atom()], typ()}.
-type subst() :: dict:dict(atom(), typ()).
-type tenv() :: {tenv, dict:dict(atom(), scheme())}.

singleton_set(A) -> sets:from_list([A]).
empty_set() -> sets:new().

dict_values(Dict) -> [ V || {_,V} <- dict:to_list(Dict) ].
dict_map(F,Dict) -> dict:map(fun(_,V) -> F(V) end, Dict).
dict_union(D1,D2) -> dict:merge(fun(_K,L,_R) -> L end, D1, D2).

null_subst() -> dict:new().

-spec ftv(typ() | scheme() | [typ()] | tenv()) -> sets:set(atom()).
ftv({tvar, N}) -> singleton_set(N);
ftv(tint) -> empty_set();
ftv(tbool) -> empty_set();
ftv({tfun, T1, T2}) -> sets:union(ftv(T1), ftv(T2));
ftv({scheme, F, T}) -> sets:subtract(ftv(T), sets:from_list(F));
ftv(Ts) when is_list(Ts) -> lists:foldr(fun sets:union/2,
                                        empty_set(),
                                        lists:map(fun ftv/1, Ts));
ftv({tenv, G}) -> ftv(dict_values(G)).


-spec sub(subst(), typ() | scheme() | [typ()] | tenv()) ->
                   typ() | scheme() | [typ()] | tenv().
sub(D,{tvar, N}) -> case dict:find(N, D) of
                        error -> {tvar, N};
                        {ok, T} -> T end;
sub(D, {tfun, T1, T2}) -> {tfun, sub(D,T1), sub(D,T2)};
sub(D, {scheme, F, T}) ->
    {scheme, F, sub(lists:foldr(fun dict:erase/2, D, F), T)};
sub(D, Ts) when is_list(Ts) -> [sub(D,T) || T <- Ts];
sub(D, {tenv,G}) -> {tenv, dict_map(fun(T) -> sub(D,T) end, G)};
sub(_,T) -> T.

-spec o(subst(), subst()) -> subst().
o(S1,S2) -> dict_union(dict_map(fun(T) -> sub(S1,T) end, S2), S1).

-spec o([subst()]) -> subst().
o(Subs) when is_list(Subs) ->
    lists:foldl(fun o/2, null_subst(), Subs).

run() -> ok.
