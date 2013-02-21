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
-module(bitpop).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-export([count/1]).

count(0) -> 0;
count(X) when is_integer(X), X > 0 -> count(X, 0).
count(0, Acc) -> Acc;
count(X, Acc) -> count((X band (X - 1)), (Acc + 1)).

-ifdef(TEST).

bitpop_test_() ->
    [?_assertEqual(0, count(0)),
     ?_assertEqual(1, count(1)),
     ?_assertEqual(2, count(3)),
     ?_assertEqual(3, count(7)),
     ?_assertEqual(4, count(15)),
     ?_assertEqual(5, count(31)),
     ?_assertEqual(6, count(63)),
     ?_assertEqual(7, count(127)),
     ?_assertEqual(8, count(255)),
     ?_assertEqual(1, count(4)),
     ?_assertEqual(1, count(8)),
     ?_assertEqual(1, count(16)),
     ?_assertEqual(1, count(32)),
     ?_assertEqual(1, count(64)),
     ?_assertEqual(1, count(128)),
     ?_assertEqual(1, count(256)),
     ?_assertEqual(1, count(512)),
     ?_assertEqual(1, count(1024)),
     ?_assertEqual(1, count(2048)),
     ?_assertEqual(1, count(16#FFFF + 1)),
     ?_assertEqual(19, count(16#FFFFE)),
     ?_assertEqual(1, count(16#FFFFF + 1)),
     ?_assertEqual(23, count(16#FFFFFE)),
     ?_assertEqual(1, count(16#FFFFF + 1)),
     ?_assertEqual(27, count(16#FFFFFFE)),
     ?_assertEqual(1, count(16#FFFFF + 1)),
     ?_assertEqual(31, count(16#FFFFFFFE)),
     ?_assertException(error, function_clause, count(-1))].

-endif.
