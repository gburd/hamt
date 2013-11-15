%% -*- coding: utf-8 -*-
%%
%% %CopyrightBegin%
%%
%% Copyright (C) 2013 Gregory Burd. All Rights Reserved.
%%
%% The contents of this file are subject to the Mozilla Public License, Version
%% 2, (the "License"); you may not use this file except in compliance with the
%% License. You should have received a copy of the Mozilla Public License along
%% with this software. If not, it can be retrieved online at
%% http://www.mozilla.org/MPL/
%%
%% Software distributed under the License is distributed on an "AS IS" basis,
%% WITHOUT WARRANTY OF ANY KIND, either express or implied. See the License for
%% the specific language governing rights and limitations under the License.
%%
%% %CopyrightEnd%
%%
%% =========================================================================
%% Ideal Hash Array Mapped Tries: an Erlang functional datatype
%%
%% The Hash Array Mapped Trie (HAMT) is based on the simple notion of hashing a
%% key and storing the key in a trie based on this hash value. The AMT is used
%% to implement the required structure e#ciently. The Array Mapped Trie (AMT)
%% is a versatile data structure and yields attractive alternative to
%% contemporary algorithms in many applications. Here I describe how it is used
%% to develop Hash Trees with near ideal characteristics that avoid the
%% traditional problem, setting the size of the initial root hash table or
%% incurring the high cost of dynamic resizing to achieve an acceptable
%% performance.
%%
%% Based on the paper "Ideal Hash Tries" by Phil Bagwell [2000].
%% @ARTICLE{Bagwell01idealhash,
%%     author = {Phil Bagwell},
%%     title = {Ideal Hash Trees},
%%     journal = {Es Grands Champs},
%%     year = {2001},
%%     volume = {1195}
%% }
%% http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.21.6279
%% http://lampwww.epfl.ch/papers/idealhashtrees.pdf
%% http://en.wikipedia.org/wiki/Hash_array_mapped_trie
%% -------------------------------------------------------------------------
%% Operations:
%%
%% - new(): returns empty hamt that uses a 32bit hash function to map
%%   keys into the trie.
%%
%% - new(32,64,128,160): returns empty hamt that uses the specified
%%   size hash function to map keys into the trie.
%%
%% - is_empty(T): returns 'true' if T is an empty hamt, and 'false'
%%   otherwise.
%%
%% - get(K, T): retrieves the value stored with key K in hamt T or
%%   `not_found' if the key is not present in the hamt.
%%
%% - put(K, V, T): inserts key K with value V into hamt T; if the key
%%   is not present in the hamt, otherwise updates key X to value V in
%%   T. Returns the new hamt.
%%
%% - delete(K, T): removes key K from hamt T; returns new hamt. Assumes
%%   that the key is present in the hamt.
%%
%% - map(F, T): maps the function F(K, V) -> V' to all key-value pairs
%%   of the hamt T and returns a new hamt T' with the same set of keys
%%   as T and the new set of values V'.
%%
%% - fold(F, T, Acc): applies the function F(K, V, Acc) -> V' to all
%%   key-value pairs of the hamt T and returns the accumulated result.
%%
-module(hamt).
-compile({no_auto_import,[put/2]}).

-ifdef(PULSE).
-compile({parse_transform, pulse_instrument}).
-endif.

-ifdef(TEST).
-ifdef(EQC).
-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_fsm.hrl").
-define(QC_OUT(P), eqc:on_output(fun(Str, Args) -> io:format(user, Str, Args) end, P)).
-endif.
-compile(export_all).
-include_lib("eunit/include/eunit.hrl").
-endif.

-export([new/0, new/1,
         is_empty/1, get/2, put/2, put/3, delete/2,
         map/2, fold/3,
         from_list/1, from_list/2, to_list/1]).

%% The Hamt data structure consists of:
%% - {hamt, nil | {SNode, CNode, LNode}}
%%   - {snode, Key::binary(), Value::binary()}
%%   - {cnode, Bitmap, Branch}
%%   - {lnode, [snode]}

-export_type([hamt/0, hamt_hash_fn/0]).

-type hamt_hashsize() :: 32 | 64 | 128 | 160.
-type hamt_hash_fn() :: {non_neg_integer(), fun((any()) -> binary())}.
-type hamt_snode()   :: {snode, any(), any()}.
-type hamt_lnode()   :: {lnode, [hamt_snode()]}.
-type hamt_cnode()   :: {cnode, non_neg_integer(),
                         [hamt_snode() | hamt_cnode() | hamt_lnode()]}.
-opaque hamt()       :: {hamt, hamt_hashsize(), nil} |
                        {hamt, hamt_hashsize(), hamt_hash_fn(), nil} |
                        {hamt, hamt_hashsize(), hamt_cnode()}.

%% @doc Returns a new, empty trie that uses
%%      32-bit hash codes for keys.
-spec new() -> hamt().
new() ->    {hamt, 32, nil}.

%% @doc Returns a new, empty trie that uses the specified
%%      number of bits when hashing keys.
-spec new(hamt_hashsize()) -> hamt().
new(HashSize) ->  {hamt, HashSize, nil}.

-spec hash(hamt_hashsize(), any()) -> non_neg_integer().
hash(HashSize, X)
  when not is_binary(X) ->
    hash(HashSize, term_to_binary(X));
hash(32,  X) -> murmur3:hash(32, X);
%hash(32,  X) -> erlang:phash2(X);
hash(64,  X) -> <<I:64/integer, _/binary>>  = crypto:sha(X), I;
hash(128, X) -> <<I:128/integer, _/binary>> = crypto:sha(X), I;
hash(160, X) -> <<I:160/integer>> = crypto:sha(X), I.

%% @doc Returns true when the trie is empty.
-spec is_empty(Hamt::hamt()) -> boolean().
is_empty({hamt, _, nil}) ->
    true;
is_empty({hamt, _, _}) ->
    false.

%% @doc This function searches for a key in a trie. Returns Value where
%%      Value is the value associated with Key, or error if the key is not
%%      present.
-spec get(Key::any(), Hamt::hamt()) -> {error, not_found} | any().
get(_Key, {hamt, _, nil}) ->
    {error, not_found};
get(Key, {hamt, _, {snode, Key, Value}}) ->
    Value;
get(_Key, {hamt, _, {snode, _, _}}) ->
    {error, not_found};
get(Key, {hamt, HashSize, {cnode, _Bitmap, _Nodes}=CN}) ->
    case get_1(hash(HashSize, Key), CN, 0, max_depth(HashSize)) of
        none ->
            {error, not_found};
        {Key, Value} ->
            Value;
        {list, List} ->
            case get_2(Key, List) of
                none ->
                    {error, not_found};
                {Key, Value} ->
                    Value;
                {_Key, _Value} ->
                    {error, not_found}
            end;
        {_Key, _Value} ->
            {error, not_found}
    end.

-spec get_1(non_neg_integer(),_,non_neg_integer(),30 | 125 | 160) -> 'none' | {_,_}.
get_1(Hash, {cnode, Bitmap, Nodes}, L, M) when L =< M ->
    Bit = bitpos(Hash, L),
    case exists(Bit, Bitmap) of
        true ->
            get_1(Hash, ba_get(index(Bit, Bitmap), Nodes), L + 5, M);
        false ->
            none
    end;
get_1(_Hash, _, L, M) when L > M ->
    none;
get_1(_Hash, {snode, Key, Value}, _L, _M) ->
    {Key, Value};
get_1(_Hash, {lnode, List}, _L, _M)
  when is_list(List) ->
    {list, List}.

-spec get_2(_,maybe_improper_list()) -> 'none' | {_,_}.
get_2(_Key, []) ->
    none;
get_2(Key, [{Key, Value} | _Rest]) ->
    {Key, Value};
get_2(Key, [{_DifferentKey, _Value} | Rest]) ->
    get_2(Key, Rest).

%% @doc This function converts the Key - Value list List to a trie.
-spec from_list([{any(), any()}]) -> hamt().
from_list(List) ->
    put(List, hamt:new()).

-spec from_list([{any(), any()}], hamt_hashsize()) -> hamt().
from_list(List, HashSize) ->
    put(List, hamt:new(HashSize)).

-spec put([{Key::any(), Value::any()}], Hamt1::hamt()) -> Hamt2::hamt().
put([], {hamt, _, _Node}=T) ->
    T;
put([{Key, Value} | Rest], {hamt, _, _Node}=T) ->
    put(Rest, put(Key, Value, T)).

%% @doc This function converts the trie to a list representation.
to_list({hamt, _, _}=T) ->
    fold(fun(Key, Value, Acc) -> [{Key, Value} | Acc] end, T, []).

%% @doc This function stores a Key - Value pair in a trie. If the Key
%%      already exists in Hamt1, the associated value is replaced by Value.
-spec put(Key::any(), Value::any(), Hamt1::hamt()) -> Hamt2::hamt().
put(Key, Value, {hamt, HashSize, nil}) ->
    {hamt, HashSize, {snode, Key, Value}};
put(Key, Value, {hamt, HashSize, Node}) ->
    {hamt, HashSize, put_1(hash(HashSize, Key), Key, Value, Node, 0, max_depth(HashSize))}.

-spec put_1(non_neg_integer(),_,_,{'lnode',maybe_improper_list()} | {'cnode',integer(),[any()]} | {'snode',_,_},non_neg_integer(),30 | 125 | 160) -> {'lnode',nonempty_maybe_improper_list()} | {'cnode',integer(),[any(),...]} | {'snode',_,_}.
put_1(Hash, Key, Value, {cnode, Bitmap, Nodes}, L, M)
  when L =< M ->
    Bit = bitpos(Hash, L),
    Idx = index(Bit, Bitmap),
    case exists(Bit, Bitmap) of
        true ->
            CN = put_1(Hash, Key, Value, ba_get(Idx, Nodes), L + 5, M),
            {cnode, Bitmap, ba_set(Idx, CN, Nodes)};
        false ->
            {cnode, (Bitmap bor Bit), ba_ins(Idx, {snode, Key, Value}, Nodes)}
    end;
put_1(_Hash, Key, Value, {snode, Key, _}, _L, _M) ->
    {snode, Key, Value};
put_1(Hash, Key, Value, {snode, SNKey, SNValue}, L, M)
  when L =< M ->
    CN = {cnode, bitpos(Hash, L), [{snode, SNKey, SNValue}]}, %% TODO: wrong hash XXX
    put_1(Hash, Key, Value, CN, L, M);
put_1(_Hash, Key1, Value1, {snode, Key2, Value2}, L, M)
  when L > M ->
    {lnode, [{Key1, Value1}, {Key2, Value2}]};
put_1(_Hash, Key, Value, {lnode, List}, _L, _M)
  when is_list(List) ->
    {lnode, [{Key, Value} | List]}.

%% @doc This function erases a given key and its value from a trie.
-spec delete(Key::any(), Hamt1::hamt()) -> Hamt2::hamt().
delete(_Key, {hamt, HashSize, nil}) ->
    {hamt, HashSize, nil};
delete(Key, {hamt, HashSize, Node}=T) ->
    Hash = hash(HashSize, Key),
    case delete_1(Hash, Key, Node, 0, max_depth(HashSize)) of
        not_found -> T;
        {snode, Key, _} -> {hamt, HashSize, nil};
        {snode, _, _}=N -> {hamt, HashSize, N};
        {cnode, _, _}=N -> {hamt, HashSize, N}
    end.

delete_1(Hash, Key, {cnode, Bitmap, Nodes}, L, M)
  when L =< M ->
    Bit = bitpos(Hash, L),
    Idx = index(Bit, Bitmap),
    case exists(Bit, Bitmap) of
        true ->
            case delete_1(Hash, Key, ba_get(Idx, Nodes), L + 5, M) of
                {cnode, _, _}=CN ->
                    {cnode, Bitmap, ba_set(Idx, CN, Nodes)};
                {snode, Key, _} ->
                    case length(Nodes) of
                        2 ->
                            [N] = ba_del(Key, Nodes), N;
                        _ ->
                            {cnode, (Bitmap bxor Bit), ba_del(Key, Nodes)}
                    end;
                {snode, _, _}=SN ->
                    case length(Nodes) > 1 of
                        true ->
                            {cnode, Bitmap, ba_set(Idx, SN, Nodes)};
                        false ->
                            SN
                    end;
                not_found ->
                    not_found
            end;
        false ->
            not_found
    end;
delete_1(_Hash, _Key, {cnode, _Bitmap, _Nodes}, L, M)
  when L > M ->
    not_found;
delete_1(_Hash, Key, {snode, Key, _}=SN, _L, _M) ->
    SN;
delete_1(_Hash, _Key, {snode, _, _}, _L, _M) ->
    not_found;
delete_1(_Hash, Key, {lnode, List}, _L, _M)
  when length(List) > 2 ->
    {lnode, lists:filter(fun({snode, K, _}) when K =:= Key -> true;
                            ({snode, _, _}) -> false end,
                         List)};
delete_1(_Hash, Key, {lnode, List}, _L, _M) ->
    {snode, Key, lists:keyfind(Key, 2, List)}.

%% @doc Map calls Fun on successive keys and values of Hamt1 to return a new
%%      value for each key. The evaluation order is undefined.
-spec map(Function, Hamt1) -> Hamt2 when % TODO
      Function :: fun((K :: term(), V1 :: term()) -> V2 :: term()),
      Hamt1 :: hamt(), Hamt2 :: hamt().
map(F, {hamt, HashSize, Node})
  when is_function(F, 2) ->
    {hamt, HashSize, map_1(F, Node)}.

map_1(_, nil) -> nil;
map_1(F, {K, V, Smaller, Larger}) ->
    {K, F(K, V), map_1(F, Smaller), map_1(F, Larger)}.

%% @doc Calls Fun on successive keys and values of a trie together with an
%%      extra argument Acc (short for accumulator). Fun must return a new
%%      accumulator which is passed to the next call. Acc0 is returned if
%%      the list is empty. The evaluation order is undefined.
-spec fold(Fun, Hamt, Acc1) -> Acc2 when
      Fun :: fun((K :: term(), V :: term(), Acc0 :: any()) -> Acc :: any()),
      Hamt :: hamt(), Acc1 :: any(), Acc2 :: any().
fold(Fun, {hamt, _, Node}, Acc) ->
    fold_1(Fun, Acc, Node).

fold_1(_F, Acc, nil) ->
    Acc;
fold_1(F, Acc, {snode, Key, Value}) ->
    F(Key, Value, Acc);
fold_1(_F, Acc, {cnode, _, []}) ->
    Acc;
fold_1(F, Acc, {cnode, _, [Node]}) ->
    fold_1(F, Acc, Node);
fold_1(F, Acc, {cnode, Bitmap, [Node | Nodes]}) ->
    fold_1(F, fold_1(F, Acc, Node), {cnode, Bitmap, Nodes});
fold_1(_F, Acc, {lnode, []}) ->
    Acc;
fold_1(F, Acc, {lnode, [{Key, Value}]}) ->
    F(Key, Value, Acc);
fold_1(F, Acc, {lnode, [{Key, Value} | KVPs]}) ->
    fold_1(F, F(Key, Value, Acc), {lnode, KVPs}).

%% Below here are other supporting functions, not public API.

ba_get(I, Nodes)
  when I =< 32, erlang:length(Nodes) =< 32 ->
    lists:nth(I, Nodes).
ba_set(1, V, [_|T]=Nodes)
  when erlang:length(Nodes) =< 32 ->
    [V|T];
ba_set(I, V, [H|T]=Nodes)
  when I =< 32, erlang:length(Nodes) =< 32 ->
    [H|ba_set(I-1, V, T)].
ba_ins(1, V, [H|T]=Nodes)
  when erlang:length(Nodes) =< 32 ->
    [V|[H|T]];
ba_ins(I, V, [H|T]=Nodes)
  when I =< 32, erlang:length(Nodes) =< 32 ->
    [H|ba_ins(I-1, V, T)];
ba_ins(1, V, [H]) -> [H, V];
ba_ins(2, V, [H]) -> [V, H];
ba_ins(_I, V, []) -> [V].
ba_del(Key, Nodes) ->
    lists:filter(fun({snode, K, _}) when K =:= Key -> false;
                    ({snode, _, _}) -> true;
                    ({cnode, _, _}) -> true;
                    ({lnode, _}) -> true
                 end, Nodes).

mask(Hash, Shift) ->
    (Hash bsr Shift) band 2#11111.

bitpos(Hash, Shift) ->
    1 bsl mask(Hash, Shift).

index(Bit, Bitmap) ->
    bitpop:count(Bitmap band (Bit - 1)) + 1.

exists(Bit, Bitmap) ->
    (Bitmap band Bit) =:= Bit.

max_depth(B)
  when B =:= 32 ->
    30;
max_depth(B)
  when B =:= 64 ->
    30;
max_depth(B)
  when B > 64 ->
    (B div 5) * 5.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-ifdef(TEST).

hamt_basics_test_() ->
    [ ?_assertEqual(true, hamt:is_empty(hamt:new())),
     ?_assertEqual(false, hamt:is_empty(hamt:put(<<"k">>, <<"v">>, hamt:new()))),
     ?_assertEqual(<<"v">>, hamt:get(<<"k">>, hamt:put(<<"k">>, <<"v">>, hamt:new()))),
     ?_assertEqual({error, not_found}, hamt:get(<<"x">>, hamt:put(<<"k">>, <<"v">>, hamt:new())))].

put_cases_split_root_snode_test() ->
    ?assertEqual(hamt:put(<<"k2">>, <<"v2">>, hamt:put(<<"k1">>, <<"v1">>, hamt:new())),
                 hamt:from_list([{<<"k1">>, <<"v1">>}, {<<"k2">>, <<"v2">>}])).

put_existing_key_replaces_value_test() ->
    ?assertEqual(hamt:get(<<"k1">>, hamt:put(<<"k1">>, <<"v'">>, hamt:put(<<"k1">>, <<"v1">>, hamt:new()))), <<"v'">>).

del_from_empty_trie_test() ->
    ?assertEqual(hamt:delete(<<"k1">>, hamt:new()), hamt:new()).

del_last_key_in_trie_test() ->
    ?assertEqual(hamt:delete(<<"k1">>, hamt:put(<<"k1">>, <<"v1">>, hamt:new())), hamt:new()).

del_one_of_many_keys_test() ->
    N = 100,
    H1 = hamt:from_list([{random:uniform(N), <<X>>} || X <- lists:seq(1,N)]),
    H2 = hamt:put(<<"k">>, <<"v">>, H1),
    H3 = hamt:delete(<<"k">>, H2),
    ?assertEqual(hamt:get(<<"k">>, H2), <<"v">>),
    ?assertEqual(lists:usort(hamt:to_list(H3)), lists:usort(hamt:to_list(H1))),
    ?assertEqual(hamt:get(<<"k">>, H3), {error, not_found}).

del_causes_cascading_cnode_collapse_test() ->
    H = hamt:put([{<<X>>, <<X>>} || X <- lists:seq(1,6)], hamt:new()),
    ?assertNotEqual(lists:usort(hamt:to_list(hamt:delete(<<5>>, H))),
                    lists:usort(hamt:to_list(H))).

put_lots_test() ->
    N = 10000, hamt:from_list([{random:uniform(N), <<X>>} || X <- lists:seq(1,N)]).

%% test() ->
%%     test(500).

%% test(NumTimes) ->
%%     eqc:quickcheck(eqc:numtests(NumTimes, prop_to_list())).

%% input_list() ->
%%     list({list(int()), int()}).

%% prop_to_list() ->
%%     ?FORALL(Xs, input_list(),
%%             equiv_to_orddict(Xs)).

%% equiv_to_orddict(Xs) ->
%%     orddict:from_list(hamt:to_list(Xs)) =:= orddict:from_list(Xs).

%% from_list(L) ->
%%     lists:foldl(fun insert_fun/2, empty(), L).

%% insert_fun({Key, Value}, Acc) ->
%%     put(Key, Value, Acc).

-endif.
