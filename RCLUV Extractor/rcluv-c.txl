% Generic RCLUV extractor
% J.R. Cordy, Queen's University
% January 2019

#pragma -w 10000000

% Spreadsheet output?
%% #define SPREADSHEET

% Column titles needed?
%% #define TITLES

% Grammar of the language we are processing
include "c.grm"

% Generic grammar for tables of nonterminal counts
define count_table
	[repeat count_table_entry] [NL]
end define

define count_table_entry
	#if not SPREADSHEET then
	    [nonterminals] [opt number] [NL]
	#else
	    #define ZEROS
	    [opt filename] [attr nonterminals] [opt number]
	#end if
end define

define filename
	[stringlit] 
end define

define nonterminals
	[repeat nonterminal+]
end define

define contents_table_entry
	[nonterminal] '= [repeat nonterminal] '; [NL]
end define

define nonterminal
	[id] | [key]
end define

redefine program
	... | [empty]
end redefine

% Main program
function main

	% List of basic nonterminals we are interested in counting
	export Nonterminals [repeat nonterminal]
		'NL	% first count is number of non-comment lines in the file
		include "nonterms-c.inc"

	% List of contained nonterminals that may be inside them
	export NonterminalContents [repeat contents_table_entry]
		include "nonterm-contains-c.inc"

	% Parse the program
	replace [program]
		P [program]

	% Compute the counts of the basic nonterminals
	export Level1 [repeat count_table_entry]
		_ [countLevel1 P each Nonterminals]

	export Level1Nonterminals [repeat nonterminal]
		_ [^ Level1]

	% Compute the counts of contained nonterminals inside them
	export Level2 [repeat count_table_entry]
		_ [countLevel2 P each Level1Nonterminals]

	construct Levels [repeat count_table_entry]
		Level1 [. Level2]

	#if TITLES and SPREADSHEET then
		% If we want just the nonterminal column titles
		construct StartTitle [list id]
			'source_file
		construct TitleLine [list id]
			StartTitle [addTitle each Levels]
				   [pragma "-raw"] [print] [pragma "-noraw"]
			  	   [quit 0]
	#end if
	
	% Get the name of the parsed input file
	import TXLinput [stringlit]
	construct LengthFilename [number]
		_ [# TXLinput] [- 8]
	construct Filename [stringlit]
		TXLinput [: 1 LengthFilename]
		
	#if SPREADSHEET then
		% Convert the output to comma-separated list (csv)
		construct File [list count_table_entry]
			Filename 
		construct Values [list count_table_entry]
			File [, each Levels] 
			     [pragma "-raw"] [print] [pragma "-noraw"]
	#else
		% Output the nonterminal counts for this input file one per line
		construct FileLine [id]
			_ [+ "source_file "] [+ "\""] [+ Filename] [+ "\""]
			  [print]
		construct ValuesLines [repeat count_table_entry]
			Levels [print]
	#end if

	by
		% rien
end function

function addTitle Entry [count_table_entry]
	deconstruct Entry 
		NT [nonterminal] MoreNTs [repeat nonterminal] _ [number]
	construct Title [id]
		_ [quote NT] 
		  [doubleUnderscore each MoreNTs] 
	replace * [list id]
		% end
	by
		Title
end function

function doubleUnderscore NT [nonterminal]
	replace [id]
		IdSoFar [id]
	by
		IdSoFar [+ "__"] [quote NT]
end function

function countLevel1 P [program] Nonterminal [nonterminal]
	construct NTid [id]
		_ [quote Nonterminal]

	export Count [number]
		0
	construct CountNTs [program]
		P [countNonterminal NTid]

	import Count

	#if not ZEROS then
	deconstruct not Count
		0
	#end if

	replace * [repeat count_table_entry]
		% end
	by
		Nonterminal Count
end function

rule countNonterminal NT [id]
	replace $ [any]
		Node [any]

	where Node [istype NT]

	import Count [number]
	export Count
		Count [+ 1]

	by
		Node 
end rule

function countLevel2 P [program] Level1NT [nonterminal]
	import Level1Nonterminals [repeat nonterminal]

	replace [repeat count_table_entry]
		Level2CountTable [repeat count_table_entry]
	by
		Level2CountTable [countEmbedded P Level1NT each Level1Nonterminals]
end function

function countEmbedded P [program] Level1NT [nonterminal] Level1NT2 [nonterminal]

	import NonterminalContents [repeat contents_table_entry]

	deconstruct * [contents_table_entry] NonterminalContents
		Level1NT '= Contents [repeat nonterminal] ';
	deconstruct * [nonterminal] Contents
		Level1NT2 

	construct Level1NTid [id]
		_ [quote Level1NT]
	construct Level1NT2id [id]
		_ [quote Level1NT2]

	export Count [number]
		0
	construct CountNTs [program]
		P [countEmbeddedNonterminal Level1NTid Level1NT2id]

	import Count

	#if not ZEROS then
	deconstruct not Count
		0
	#end if

	replace * [repeat count_table_entry]
		% end
	by
		Level1NT Level1NT2 Count
end function

rule countEmbeddedNonterminal NTid [id] EmbeddedNTid [id]
	import Level1 [repeat count_table_entry]

	deconstruct not * [count_table_entry] Level1
		NTid 0
	deconstruct not * [count_table_entry] Level1
		EmbeddedNTid 0

	replace $ [any]
		Node [any]

	where Node [istype NTid]

	by 
		Node [countNonterminal EmbeddedNTid]
		     [subtractSelf NTid EmbeddedNTid]
end rule

function subtractSelf NT1id [id] NT2id [id]
	deconstruct NT1id
		NT2id
	import Count [number]
	export Count
		Count [- 1]
	match [any]
		_ [any]
end function
