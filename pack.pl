/**
 * pack.pl - SWI-Prolog Pack Manifest
 * 
 * This file defines the metadata for the TRILL SWI-Prolog pack.
 * It is used by the SWI-Prolog package manager to identify, install,
 * and manage the TRILL probabilistic reasoning library.
 * 
 * TRILL (Tableau Reasoner for descrIption Logics in Prolog) provides
 * three different tableau-based reasoners for probabilistic description
 * logic knowledge bases:
 *   - TRILL: finds all explanations using standard DFS backtracking
 *   - TRILLP: computes a pinpointing formula (Boolean formula over axioms)
 *   - TORNADO: builds BDDs during the expansion phase
 * 
 * @author Riccardo Zese
 * @license Artistic License 2.0
 * @copyright Riccardo Zese
 */

%% name(?Name:atom)
%
%  Defines the pack name used by the SWI-Prolog package manager.
%  The pack is identified as 'trill'.
name(trill).

%% title(?Title:string)
%
%  Provides a human-readable description of the pack.
%  This is displayed when listing or searching for packs.
title('A tableau probabilistic reasoner in three different versions').

%% version(?Version:string)
%
%  Specifies the current version of the pack in semantic versioning format.
version('8.0.0').

%% author(?Name:string, ?Email:string)
%
%  Identifies the author of the pack with their name and email address.
author('Riccardo Zese', 'zsercr@unife.it').

%% download(?URL:string)
%
%  Provides the URL pattern for downloading the pack releases.
%  The wildcard (*) matches different version releases.
download('https://github.com/rzese/trill/releases/*.zip').

%% requires(?PackName:atom)
%
%  Declares the dependencies required by this pack.
%  TRILL requires the BDDEM pack for Binary Decision Diagram
%  based probability computation.
requires(bddem).
