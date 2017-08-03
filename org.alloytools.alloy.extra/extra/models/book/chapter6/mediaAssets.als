module chapter6/mediaAssets

sig ApplicationState {
	catalogs: set Catalog,
	catalogState: catalogs -> one CatalogState,
	currentCatalog: catalogs,
	buffer: set Asset
	}

sig Catalog, Asset {}

sig CatalogState {
	assets: set Asset,
	disj hidden, showing: set assets,
	selection: set assets + Undefined
	} {
	hidden+showing = assets
	}

one sig Undefined {}

pred catalogInv [cs: CatalogState] {
	cs.selection = Undefined or (some cs.selection and cs.selection in cs.showing)
	}

pred appInv [xs: ApplicationState] {
	all cs: xs.catalogs | catalogInv [xs.catalogState[cs]]
	}

pred showSelected [cs, cs': CatalogState] {
	cs.selection != Undefined
	cs'.showing = cs.selection
	cs'.selection = cs.selection
	cs'.assets = cs.assets
	}

pred hideSelected [cs, cs': CatalogState] {
	cs.selection != Undefined
	cs'.hidden = cs.hidden + cs.selection
	cs'.selection = Undefined
	cs'.assets = cs.assets
	}

pred cut [xs, xs': ApplicationState] {
	let cs = xs.currentCatalog.(xs.catalogState), sel = cs.selection {
		sel != Undefined
		xs'.buffer = sel
		some cs': CatalogState {
			cs'.assets = cs.assets - sel
			cs'.showing = cs.showing - sel
			cs'.selection = Undefined
			xs'.catalogState = xs.catalogState ++ xs.currentCatalog -> cs'
			}
		}
	xs'.catalogs = xs.catalogs
	xs'.currentCatalog = xs.currentCatalog
	}

pred paste [xs, xs': ApplicationState] {
	let cs = xs.currentCatalog.(xs.catalogState), buf = xs.buffer {
		xs'.buffer = buf
		some cs': CatalogState {
			cs'.assets = cs.assets + buf
			cs'.showing = cs.showing + (buf - cs.assets)
			cs'.selection = buf - cs.assets
			xs'.catalogState = xs.catalogState ++ xs.currentCatalog -> cs'
			}
		}
	xs'.catalogs = xs.catalogs
	xs'.currentCatalog = xs.currentCatalog
	}

assert HidePreservesInv {
	all cs, cs': CatalogState |
		catalogInv [cs] and hideSelected [cs, cs'] => catalogInv [cs']
	}

// This check should not find any counterexample
check HidePreservesInv

pred sameApplicationState [xs, xs': ApplicationState] {
	xs'.catalogs = xs.catalogs
	all c: xs.catalogs | sameCatalogState [c.(xs.catalogState), c.(xs'.catalogState)]
	xs'.currentCatalog = xs.currentCatalog
	xs'.buffer = xs.buffer
	}

pred sameCatalogState [cs, cs': CatalogState] {
	cs'.assets = cs.assets
	cs'.showing = cs.showing
	cs'.selection = cs.selection
	}

assert CutPaste {
	all xs, xs', xs": ApplicationState |
		(appInv [xs] and cut [xs, xs'] and paste [xs', xs"]) => sameApplicationState [xs, xs"] 
	}

// This check should find a counterexample
check CutPaste

assert PasteCut {
	all xs, xs', xs": ApplicationState |
		(appInv [xs] and paste [xs, xs'] and cut [xs', xs"]) => sameApplicationState [xs, xs"] 
	}

// This check should find a counterexample
check PasteCut

assert PasteNotAffectHidden {
	all xs, xs': ApplicationState |
		(appInv [xs] and paste [xs, xs']) => 
			let c = xs.currentCatalog | xs'.catalogState[c].hidden = xs.catalogState[c].hidden
	}

// This check should not find any counterexample
check PasteNotAffectHidden
