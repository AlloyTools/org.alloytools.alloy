sig A, B {}

one sig G {
	aone_oneb : A one -> one B,
	aone_loneb : A one -> lone B,
	aone_someb : A one -> some B,
	aone_setb : A one -> some B,

	alone_oneb : A lone -> one B,
	alone_loneb : A lone -> lone B,
	alone_someb : A lone -> some B,
	alone_setb : A lone -> some B,

	asome_oneb : A some -> one B,
	asome_loneb : A some -> lone B,
	asome_someb : A some -> some B,
	asome_setb : A some -> some B,

	aset_oneb : A set -> one B,
	aset_loneb : A set -> lone B,
	aset_someb : A set -> some B,
	aset_setb : A set -> some B,

} 

run {} for 3 but exactly 3 A
