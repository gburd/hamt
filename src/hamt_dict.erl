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
-module(hamt_dict).
-author('Steve Vinoski <vinoski@ieee.org>').

-export([append/3, append_list/3, erase/2, fetch/2,
         fetch_keys/1, filter/2, find/2, fold/3,
         from_list/1, is_key/2, map/2, merge/3,
         new/0, size/1, store/3, to_list/1,
         update/3, update/4, update_counter/3]).

append(Key, Value, Dict) ->
    NewVal = case hamt:get(Key, Dict) of
                 {error, not_found} ->
                     [Value];
                 OldVal ->
                     OldVal ++ [Value]
             end,
    hamt:put(Key, NewVal, Dict).

append_list(Key, ValList, Dict) when is_list(ValList) ->
    NewVal = case hamt:get(Key, Dict) of
                 {error, not_found} ->
                     ValList;
                 OldVal when is_list(OldVal) ->
                     OldVal ++ ValList;
                 _ ->
                     error(badarg)
             end,
    hamt:put(Key, NewVal, Dict).

erase(Key, Dict) ->
    hamt:delete(Key, Dict).

fetch(Key, Dict) ->
    case hamt:get(Key, Dict) of
        {error, not_found} ->
            error(badarg);
        Value ->
            Value
    end.

fetch_keys(Dict) ->
    hamt:fold(fun(Key, _, Acc) -> [Key|Acc] end, Dict, []).

filter(Pred, Dict) ->
    Fold = fun(Key, Value, Acc) ->
                   case Pred(Key, Value) of
                       true ->
                           hamt:put(Key, Value, Acc);
                       _ ->
                           Acc
                   end
           end,
    hamt:fold(Fold, Dict, hamt:new()).

find(Key, Dict) ->
    case hamt:get(Key, Dict) of
        {error, not_found} ->
            error;
        Value ->
            {ok, Value}
    end.

fold(Fun, Acc0, Dict) ->
    hamt:fold(Fun, Dict, Acc0).

from_list(List) ->
    hamt:from_list(List).

is_key(Key, Dict) ->
    case hamt:get(Key, Dict) of
        {error, not_found} ->
            false;
        _ ->
            true
    end.

map(Fun, Dict) ->
    hamt:map(Fun, Dict).

merge(Fun, Dict1, Dict2) ->
    hamt:fold(fun(Key, Val1, Dict) ->
                      update(Key, fun(Val2) -> Fun(Key, Val1, Val2) end, Val1, Dict)
              end, Dict2, Dict1).

new() ->
    hamt:new().

size(Dict) ->
    hamt:fold(fun(_, _, Acc) -> Acc+1 end, Dict, 0).

store(Key, Value, Dict) ->
    hamt:put(Key, Value, Dict).

to_list(Dict) ->
    hamt:to_list(Dict).

update(Key, Fun, Dict) ->
    case hamt:get(Key, Dict) of
        {error, not_found} ->
            error(badarg);
        Value ->
            hamt:put(Key, Fun(Value), Dict)
    end.

update(Key, Fun, Initial, Dict) ->
    NewVal = case hamt:get(Key, Dict) of
                 {error, not_found} ->
                     Initial;
                 Value ->
                     Fun(Value)
             end,
    hamt:put(Key, NewVal, Dict).

update_counter(Key, Increment, Dict) ->
    NewVal = case hamt:get(Key, Dict) of
                 {error, not_found} ->
                     Increment;
                 Value ->
                     Value+Increment
             end,
    hamt:put(Key, NewVal, Dict).
