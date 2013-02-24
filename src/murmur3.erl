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

%% Inspired by:
%% https://github.com/PeterScott/murmur3/blob/master/murmur3.c
%% https://raw.github.com/rdamodharan/redbloom/master/src/murmur3.erl

-module(murmur3).
-export([hash/1, hash/2, hash/3]).

-define(MASK32, 16#FFFFFFFF).

rotl32(Num, R) -> ((Num bsl R) bor (Num bsr (32 - R))) band ?MASK32.

hash32_mmix(K1) ->
    K2 = (K1 * 16#CC9E2D51) band ?MASK32,
    K3 = rotl32(K2, 15),
    (K3 * 16#1B873593) band ?MASK32.

hash32_fmix(H) ->
    H2 = ((H bxor (H bsr 16)) * 16#85EBCA6B) band ?MASK32,
    H3 = ((H2 bxor (H2 bsr 13)) * 16#C2B2AE35) band ?MASK32,
    H3 bxor (H3 bsr 16).

hash32_tail_mix(K1, Hash) ->
    Hash bxor hash32_mmix(K1).

% 4-byte blocks
hash32_body(<<K1:32/little, Rest/binary>>, Hash) ->
    K2 = hash32_mmix(K1),
    Hash2 = Hash bxor K2,
    Hash3 = rotl32(Hash2, 13),
    Hash4 = (Hash3 * 5 + 16#E6546B64) band ?MASK32,
    hash32_body(Rest, Hash4);
% Tail of the data (1-,2-,3- byte blocks)
hash32_body(<<K1:8>>, Hash) -> hash32_tail_mix(K1, Hash);
hash32_body(<<K1:16/little>>, Hash) -> hash32_tail_mix(K1, Hash);
hash32_body(<<K1:24/little>>, Hash) -> hash32_tail_mix(K1, Hash);
hash32_body(<<>>, Hash) -> Hash.

hash32_impl(Data, Seed) ->
    Len = byte_size(Data),
    hash32_fmix(hash32_body(Data, Seed) bxor Len).

hash32(Data, Seed) when is_binary(Data) -> hash32_impl(Data, Seed);
hash32(Data, Seed) -> hash32(term_to_binary(Data), Seed).

hash32(Data) -> hash32(Data, 16#9E3779B9). % Seed is "golden ratio" FWIW.

hash(Data) -> hash32(Data).
hash(32, Data) -> hash32(Data).
hash(32, Data, Seed) -> hash32(Data, Seed).
