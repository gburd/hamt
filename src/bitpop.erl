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

-ifdef(WORKING_METHOD_1). % Slow, but effective.
count(0) -> 0;
count(X) when is_integer(X), X > 0 -> count(X, 0).
count(0, Acc) -> Acc;
count(X, Acc) -> count((X band (X - 1)), (Acc + 1)).
-endif.

%-ifdef(WORKING_METHOD_2). % Works well enough
-spec count(non_neg_integer()) -> char().
-spec c1(pos_integer()) -> integer().
-spec c2(pos_integer()) -> non_neg_integer().
-spec c3(pos_integer()) -> non_neg_integer().
-spec c4(pos_integer()) -> non_neg_integer().
count(0) -> 0;
count(X)
  when is_integer(X), X > 0, X < 16#FFFFFFFF ->
    ((c4(X) bsr 16) + c4(X)) band 16#0000FFFF.
c1(V) -> V - ((V bsr 1) band 16#55555555).
c2(V) -> ((c1(V) bsr 2) band 16#33333333) + (c1(V) band 16#33333333).
c3(V) -> ((c2(V) bsr 4) + c2(V)) band 16#0F0F0F0F.
c4(V) -> ((c3(V) bsr 8) + c3(V)) band 16#00FF00FF.
%-endif.

-ifdef(NOT_YET_WORKING_METHOD_3). % Might be faster than method 2
count(0) -> 0;
count(X) when is_integer(X), X > 0, X =< 16#FFFFFFFF ->
    ((c2(X) + (c2(X) bsr 4) band 16#0F0F0F0F) * 16#01010101) bsr 24.
c1(V) -> V - ((V bsr 1) band 16#55555555).
c2(V) -> (c1(V) band 16#33333333) + ((c1(V) bsr 2) band 16#33333333).
-endif.

-ifdef(NOT_YET_WORKING_METHOD_3_64bit).
count(X) when is_integer(X) -> %, X > 16#FFFFFFFF, X =< 16#FFFFFFFFFFFFFFFF ->
    M1  = 16#5555555555555555, %% 0101...
    M2  = 16#3333333333333333, %% 00110011..
    M4  = 16#0f0f0f0f0f0f0f0f, %% 4 zeros,  4 ones ...
    H01 = 16#0101010101010101, %% the sum of 256 to the power of 0,1,2,3...

    %% 1. put count of each 2 bits into those 2 bits
    X1 = X - (X bsr 1) band M1,
    %% 2. put count of each 4 bits into those 4 bits
    X2 = (X1 band M2) + ((X1 bsr 2) band M2),
    %% 3. put count of each 8 bits into those 8 bits
    X3 = (X2 + (X2 bsr 4)) band M4,
    %% 4. returns left 8 bits of x + (x<<8) + (x<<16) + (x<<24) + ...
    (X3 * H01) bsr 56.
-endif.

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
