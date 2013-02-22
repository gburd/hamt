%% -*- coding: utf-8 -*-
%%
%% %CopyrightBegin%
%%
%% Copyright (C) 2013 Gregory Burd. All Rights Reserved.
%%
%% The contents of this file are subject to the Mozilla Public License,
%% Version 2, (the "License"); you may not use this file except in
%% compliance with the License. You should have received a copy of the
%% Mozilla Public License along with this software. If not, it can be
%% retrieved online at http://www.mozilla.org/MPL/
%%
%% Software distributed under the License is distributed on an "AS IS"
%% basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See
%% the License for the specific language governing rights and limitations
%% under the License.
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
%% - new(): returns empty hamt.
%%
%% - is_empty(T): returns 'true' if T is an empty hamt, and 'false'
%%   otherwise.
%%
%% - get(K, T): retreives the value stored with key K in hamt T or
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
%include_lib("eqc/include/eqc.hrl").
%include_lib("eqc/include/eqc_fsm.hrl").
-endif.
-compile(export_all).
-include_lib("eunit/include/eunit.hrl").
-endif.

-export([new/0, is_empty/1, get/2, put/2, put/3, delete/2,
         map/2, fold/3,
         from_list/1, to_list/1]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% The Hamt data structure consists of:
%% - {hamt, nil | {SNode, CNode, LNode}
%%   - {snode, Key::binary(), Value::binary()}
%%   - {cnode, Bitmap, Branch}
%%   - {lnode, [snode]}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Some types.

-export_type([hamt/0]).

-type hamt_snode() :: {snode, binary(), binary()}.
-type hamt_lnode() :: {lnode, [hamt_snode()]}.
-type hamt_cnode() :: {cnode, non_neg_integer(), [hamt_snode() | hamt_cnode() | hamt_lnode()]}.
-opaque hamt()     :: {hamt, non_neg_integer(), nil | hamt_cnode()}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-spec new() -> hamt().

new() ->
    {hamt, nil}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-spec is_empty(Hamt) -> boolean() when
      Hamt :: hamt().

is_empty({hamt, nil}) ->
    true;
is_empty(_) ->
    false.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-spec get(Key, Hamt) -> not_found | Value when
      Key   :: binary(),
      Value :: binary(),
      Hamt  :: hamt().

get(_Key, {hamt, nil}) ->
    not_found;
get(Key, {hamt, {snode, Key, Value}}) ->
    Value;
get(Key, {hamt, {cnode, _Bitmap, _Nodes}=CN}) ->
    case get_1(hash(Key), CN, 0) of
        none ->
            not_found;
        {Key, Value} ->
            Value;
        {list, List} ->
            case get_2(Key, List) of
                none -> not_found;
                {Key, Value} -> Value;
                {_Key, _Value} -> not_found
            end;
        {_Key, _Value} ->
            not_found
    end.

get_1(H, {cnode, Bitmap, Nodes}, L) ->
    Bit = bitpos(H, L),
    case exists(Bit, Bitmap) of
        true -> get_1(H, ba_get(index(Bit, Bitmap), Nodes), L + 5);
        false -> none
    end;
get_1(_H, {snode, Key, Value}, _L) ->
    {Key, Value};
get_1(_H, {lnode, List}, _L) when is_list(List) ->
    {list, List}.

get_2(_Key, []) ->
    none;
get_2(Key, [{Key, Value} | _Rest]) ->
    {Key, Value};
get_2(Key, [{_DifferentKey, _Value} | Rest]) ->
    get_2(Key, Rest).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

from_list(L) ->
    put(L, hamt:new()).

to_list({hamt, _}=T) ->
    fold(fun(Key, Value, Acc) -> [{Key, Value} | Acc] end, T, []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-spec put([{Key, Value}], Hamt1) -> Hamt2 when
      Key   :: binary(),
      Value :: binary(),
      Hamt1 :: hamt(),
      Hamt2 :: hamt().

put([], {hamt, _Node}=T) ->
    T;
put([{Key, Value} | Rest], {hamt, _Node}=T) ->
    put(Rest, put(Key, Value, T)).

-spec put(Key, Value, Hamt1) -> Hamt2 when
      Key   :: binary(),
      Value :: binary(),
      Hamt1 :: hamt(),
      Hamt2 :: hamt().

put(Key, Value, {hamt, nil})
  when is_binary(Key), is_binary(Value) ->
    {hamt, {snode, Key, Value}};
put(Key, Value, {hamt, Node})
  when is_binary(Key), is_binary(Value) ->
    {hamt, put_1(hash(Key), Key, Value, Node, 0)}.

put_1(H, Key, Value, {cnode, Bitmap, Nodes}, L) when is_integer(L), L =< 30 ->
    Bit = bitpos(H, L),
    Idx = index(Bit, Bitmap),
    case exists(Bit, Bitmap) of
        true ->
            CN = put_1(H, Key, Value, ba_get(Idx, Nodes), L + 5),
            {cnode, Bitmap, ba_set(Idx, CN, Nodes)};
        false ->
            {cnode, (Bitmap bor Bit), ba_ins(Idx, {snode, Key, Value}, Nodes)}
    end;
put_1(_H, Key, Value, {snode, Key, _}, _L) ->
    {snode, Key, Value};
put_1(H, Key, Value, {snode, SNKey, SNValue}, L) when is_integer(L), L =< 30 ->
    put_1(H, Key, Value, split(SNKey, SNValue, L), L);
put_1(_H, Key, Value, {snode, _, _}, L) when L > 30 ->
    {lnode, [{Key, Value}]};
put_1(_H, Key, Value, {lnode, List}, _L) when is_list(List) ->
    {lnode, [{Key, Value} | List]}.

split(SNKey, SNValue, L) ->
    {cnode, bitpos(hash(SNKey), L), [{snode, SNKey, SNValue}]}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-spec delete(Key, Hamt1) -> Hamt2 when
      Key :: binary(),
      Hamt1 :: hamt(),
      Hamt2 :: hamt().

delete(Key, {hamt, nil})
  when is_binary(Key) ->
    {hamt, nil};
delete(Key, {hamt, Node}=T)
  when is_binary(Key) ->
    case delete_1(hash(Key), Key, Node, 0) of
        not_found -> T;
        {snode, Key, _} -> {hamt, nil};
        {snode, _, _}=N -> {hamt, N};
        {cnode, _, _}=N -> {hamt, N}
    end.

delete_1(H, Key, {cnode, Bitmap, Nodes}, L)
  when is_integer(L), L =< 30 ->
    Bit = bitpos(H, L),
    Idx = index(Bit, Bitmap),
    case exists(Bit, Bitmap) of
        true ->
            case delete_1(H, Key, ba_get(Idx, Nodes), L + 5) of
                {cnode, _, _}=CN ->
                    {cnode, Bitmap, ba_set(Idx, CN, Nodes)};
                {snode, Key, _} ->
                    case length(Nodes) of
                        2 ->
                            [{snode, _, _}=SN] = ba_del(Key, Nodes),
                            SN;
                        false ->
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
delete_1(_H, Key, {snode, Key, _}=SN, _L) ->
    SN;
delete_1(_H, _Key, {snode, _, _}, _L) ->
    not_found;
delete_1(_H, Key, {lnode, List}, _L) ->
    case length(List) > 2 of
        true ->
            {lnode, lists:filter(fun({snode, K, _}) when K =:= Key -> true;
                                    ({snode, _, _}) -> false end,
                                 List)};
        false ->
            {snode, Key, lists:keyfind(Key, 2, List)}
    end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-spec map(Function, Hamt1) -> Hamt2 when
      Function :: fun((K :: term(), V1 :: term()) -> V2 :: term()),
      Hamt1 :: hamt(),
      Hamt2 :: hamt().

map(F, {hamt, _}=T) when is_function(F, 2) ->
    {map_1(F, T)}.

map_1(_, nil) -> nil;
map_1(F, {K, V, Smaller, Larger}) ->
    {K, F(K, V), map_1(F, Smaller), map_1(F, Larger)}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-spec fold(Function, Hamt, Acc) -> Hamt when
      Function :: fun((K :: term(), V :: term()) -> V2 :: term()),
      Hamt :: hamt(),
      Acc :: any().

fold(Function, {hamt, Node}, Acc) ->
    fold_1(Function, Acc, Node).

fold_1(F, Acc, {snode, Key, Value}) ->
    F(Key, Value, Acc);
fold_1(_F, Acc, {cnode, _, []}) ->
    Acc;
fold_1(F, Acc, {cnode, _, [Node]}) ->
    fold_1(F, Acc, Node);
fold_1(F, Acc, {cnode, Bitmap, [Node | Nodes]}) ->
    fold_1(F, fold_1(F, Acc, Node), {cnode, Bitmap, Nodes});
fold_1(F, Acc, {lnode, Nodes}) ->
    lists:foldl(F, Acc, Nodes).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

mask(Hash, Shift) ->
    (Hash bsr Shift) band 2#11111.

bitpos(Hash, Shift) ->
    1 bsl mask(Hash, Shift).

index(Bit, Bitmap) ->
    bitpop:count(Bitmap band (Bit - 1)) + 1. % Arrays start with index 1, not 0

exists(Bit, Bitmap) ->
    (Bitmap band Bit) =:= Bit.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

hash(Key) when is_binary(Key) ->
    erlang:phash2(Key).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-ifdef(TEST).

create_a_hamt_test_() ->
    [?_assertEqual({hamt, nil}, hamt:new()),
     ?_assertEqual(true, hamt:is_empty(hamt:new())),
     ?_assertEqual(false, hamt:is_empty(hamt:put(<<"k">>, <<"v">>, hamt:new()))),
     ?_assertEqual(<<"v">>, hamt:get(<<"k">>, hamt:put(<<"k">>, <<"v">>, hamt:new())))].

put_causes_split_root_snode_test() ->
    ?assertEqual(hamt:put(<<"k2">>, <<"v2">>, {hamt,{snode,<<"k1">>,<<"v1">>}}),
                 {hamt,{cnode,4456448,
                        [{snode,<<"k1">>,<<"v1">>},{snode,<<"k2">>,<<"v2">>}]}}).

put_causes_2_splits_test() ->
    ?assertEqual(hamt:put(<<5>>,<<5>>,{hamt,{cnode,17563904,
                                             [{snode,<<3>>,<<3>>},
                                              {snode,<<1>>,<<1>>},
                                              {snode,<<2>>,<<2>>},
                                              {snode,<<4>>,<<4>>}]}}),
                 {hamt,
                  {cnode,17563904,
                   [{snode,<<3>>,<<3>>},
                    {snode,<<1>>,<<1>>},
                    {cnode,131072,
                     [{cnode,142606336,
                       [{snode,<<2>>,<<2>>},
                        {snode,<<5>>,<<5>>}]}]},
                    {snode,<<4>>,<<4>>}]}}).

put_existing_key_replaces_value_test() ->
    ?assertEqual(hamt:put(<<"k1">>, <<"v'">>,
                          {hamt,{cnode,4456448,
                                 [{snode,<<"k1">>,<<"v1">>},{snode,<<"k2">>,<<"v2">>}]}}),
                          {hamt,{cnode,4456448,
                                 [{snode,<<"k1">>,<<"v'">>},{snode,<<"k2">>,<<"v2">>}]}}).

del_from_empty_trie_test() ->
    ?assertEqual(hamt:delete(<<"k1">>, {hamt, nil}), {hamt, nil}).

del_last_key_in_trie_test() ->
    ?assertEqual(hamt:delete(<<"k1">>, {hamt,{snode,<<"k1">>,<<"v1">>}}), {hamt, nil}).

del_one_of_many_keys_test() ->
    ?assertEqual(hamt:delete(<<"k1">>,
                             {hamt,{cnode,4456448,
                                    [{snode,<<"k1">>,<<"v1">>},
                                     {snode,<<"k2">>,<<"v2">>}]}}),
                 {hamt,{snode,<<"k2">>,<<"v2">>}}).

del_causes_cascading_cnode_collapse_test() ->
    ?assertEqual(hamt:delete(<<5>>, hamt:put([{<<X>>, <<X>>} || X <- lists:seq(1,6)], hamt:new())),
                 {hamt,{cnode,17629440,
                        [{snode,<<3>>,<<3>>},
                         {snode,<<6>>,<<6>>},
                         {snode,<<1>>,<<1>>},
                         {snode,<<2>>,<<2>>},
                         {snode,<<4>>,<<4>>}]}}).

put_lots_test() ->
    KVPs = [{<<X>>, <<X>>} || X <- lists:seq(1,10000)],
    hamt:put(KVPs, hamt:new()).

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
