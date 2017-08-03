module VSR/flashDevice [Data]

// Alloy model of the flash hardware
// Based on the Open NAND Flash Interface 2.0
// Author: Eunsuk Kang, Mar. 2008

open util/ordering[EraseFrequency] as EFO
open util/seqrel[LUN] as LSeq
open util/seqrel[Block] as BSeq
open util/seqrel[Page] as PSeq

one sig ErasedData in Data {}

// In ABZ paper, each field in RowAddr is an integer;
// Here, instead, we represent these numeric indices using SeqIdx atoms
// for higher abstraction.  This does not change the semantics of the flash model.
sig RowAddr {
	l : LSeq/SeqIdx,			// LUN address
	b : BSeq/SeqIdx,		// block address
	p : PSeq/SeqIdx		// page address
}
{
	#LSeq/ord/prevs[l] < DEVICE_SIZE
	#BSeq/ord/prevs[b] < LUN_SIZE
	#PSeq/ord/prevs[p] < BLOCK_SIZE
}

abstract sig PageStatus {}

one sig Free,			// erased and ready to be programmed 
			Allocated, 	// allocated for a file write operation
			Valid, 			// contains valid data in a file
			Invalid 			// contains obsolete data
			extends PageStatus {}

// smallest unit for read & program
sig Page {
	data : seq Data
}
{
	#data = PAGE_SIZE
}

// erase frequency for wear-leveling
abstract sig EraseFrequency {}
// rather coarse abstraction of wear on each block
one sig NeverErased, SeldomErased, OftenErased extends EraseFrequency {}

fact EraseFrequencyOrdering{
	EFO/first[] = NeverErased
	EFO/last[] = OftenErased
}

// smallest unit for erasure
sig Block {
	pages : PSeq/SeqIdx -> Page
}
{
	PSeq/isSeq[pages]
	#pages = BLOCK_SIZE
}

sig LUN {
	blocks : BSeq/SeqIdx -> Block
}
{
	BSeq/isSeq[blocks]
	#blocks = LUN_SIZE
}

sig Device {
	luns : LSeq/SeqIdx -> LUN,
	pageStatusMap : RowAddr -> one PageStatus,
	// In ABZ paper, eraseFreqMap is replaced by eraseCountMap,
	// which maps each block to the number of times it has been erased.
	// We further abstract the erase count by representing it with three
	// different categories, "NeverErased, "SeldomErased", and "OftenErased".
	eraseFreqMap : BSeq/SeqIdx -> one EraseFrequency,
	reserveBlock : BSeq/SeqIdx
}
{
	LSeq/isSeq[luns]	
	#luns = DEVICE_SIZE
}

/********************
 * Frame conditions & other auxiliary functions
 ********************/
// Only one block may change its state - 
// Everything else inside the LUN must stay the same
pred LUNFrameCond[d, d' : Device, modifiedBlock : Block, 
						newEraseFreq : EraseFrequency, newReclaimBlock : BSeq/SeqIdx,
						rowAddr : RowAddr] {
	let lunAddr = rowAddr.l, blockAddr = rowAddr.b, 
		 lun = d.luns[lunAddr], lun' = d'.luns[lunAddr]  {
		 	lun'.blocks = lun.blocks ++ (blockAddr -> modifiedBlock)
			d'.luns = d.luns ++ (lunAddr -> lun')
			d'.eraseFreqMap = d.eraseFreqMap ++ (blockAddr -> newEraseFreq)
			d'.reserveBlock = newReclaimBlock
	} 
}

// Only one page may change its state -
// Everything else inside the block must stay the same
pred blockFrameCond[d, d' : Device, modifiedPage : Page, rowAddr : RowAddr] {
	let lunAddr = rowAddr.l, blockAddr = rowAddr.b, pageAddr = rowAddr.p,
		 lun = d.luns[lunAddr], lun' = d'.luns[lunAddr],
		 block = lun.blocks[blockAddr], block' = lun'.blocks[blockAddr],
		 eraseFreq = d.eraseFreqMap[blockAddr],
		 reserveBlock = d.reserveBlock {
		 	block'.pages = block.pages ++ (pageAddr -> modifiedPage)
		 	LUNFrameCond[d, d', block', eraseFreq, reserveBlock, rowAddr]
	}
}

// Update the status of the specified page to Valid
// No change to the data within the page
pred validatePage[d, d' : Device, rowAddr : RowAddr] {
	let lunAddr = rowAddr.l, blockAddr = rowAddr.b, pageAddr = rowAddr.p,
		page = d.luns[lunAddr].blocks[blockAddr].pages[pageAddr],
		page' = d'.luns[lunAddr].blocks[blockAddr].pages[pageAddr] | 
			(page'.data = page.data and
			 d'.pageStatusMap[rowAddr] = Valid)
}

// Update the status of the specified page to Invalid
// No change to the data within the page
pred invalidatePage[d, d' : Device, rowAddr : RowAddr] {
	let lunAddr = rowAddr.l, blockAddr = rowAddr.b, pageAddr = rowAddr.p,
		 page = d.luns[lunAddr].blocks[blockAddr].pages[pageAddr],
		 page' = d'.luns[lunAddr].blocks[blockAddr].pages[pageAddr] | 
		 	(page'.data = page.data and
			 d'.pageStatusMap[rowAddr] = Invalid)			
}

// The page does not change between two device states
pred fixPage[d, d' : Device, rowAddr : RowAddr] {
	let lunAddr = rowAddr.l, blockAddr = rowAddr.b, pageAddr = rowAddr.p,
		 page = d.luns[lunAddr].blocks[blockAddr].pages[pageAddr],
		 page' = d'.luns[lunAddr].blocks[blockAddr].pages[pageAddr] | 
		 	(page'.data = page.data and 
			 d.pageStatusMap[rowAddr] = d'.pageStatusMap[rowAddr])			
}

// The erase frequency of each block remains the same
pred fixEraseFrequencies[d, d' : Device] {
	d'.eraseFreqMap = d.eraseFreqMap
	d'.reserveBlock = d.reserveBlock
}

fun readEraseFreq[d : Device, rowAddr : RowAddr] : EraseFrequency {
	let blockAddr = rowAddr.b |
		d.eraseFreqMap[blockAddr]
}

// Wear-leveling technique
// Select the least erased out of all erase units that contain any obsolete blocks
fun selectLeastErasedUnit[d : Device] : BSeq/SeqIdx {

	let dirtyPageAddrs = d.pageStatusMap.Invalid,
		 dirtyUnitAddrs = dirtyPageAddrs.b,
		 dirtyUnitEraseFrequencies = d.eraseFreqMap[dirtyUnitAddrs],
		 minEraseFreq = min[dirtyUnitEraseFrequencies] |

		 // the set of dirty units with the lowest erase frequency
		 d.eraseFreqMap.minEraseFreq

}

/********************
 * Main Flash-API functions
 ********************/

// Program a page or a portion of a page of data specified by colAddr
// A page-level operation - success case
// Normal sequence of operations:
// 1. The page status flag is set to "Used"
// 2. The input data is programmed at the corresponding address
// 3. The page status flag is set to "Valid" (i.e. ready for read)
pred fProgram[d, d' : Device, colAddr : Int, rowAddr : RowAddr, programData : seq Data]{
	// preconditions
	0 <= colAddr
	colAddr < PAGE_SIZE

	some modifiedPage : Page |
		let lunAddr = rowAddr.l, blockAddr = rowAddr.b, pageAddr = rowAddr.p,
			page = d.luns[lunAddr].blocks[blockAddr].pages[pageAddr],
			// existing page data in positions that precede the "colAddr" offset
			prefixData = (page.data).subseq[0, sub[colAddr,1]],	
			// truncate all of input data that exceed the page size
			trucData = (programData).subseq[0,sub[sub[
												PAGE_SIZE, colAddr], 1]] {
				d.pageStatusMap[rowAddr] = Free and
				d'.pageStatusMap = 
					d.pageStatusMap ++ (rowAddr -> Allocated)
				modifiedPage.data = prefixData.append[trucData]
				blockFrameCond[d, d', modifiedPage, rowAddr]
			} 
}

// Read data starting at colAddr within the page specified by RowAddr
// A page-level operation
// Success case
fun fRead [d : Device, colAddr : Int, rowAddr : RowAddr] : seq Data {
	let lunAddr = rowAddr.l, blockAddr = rowAddr.b, pageAddr = rowAddr.p,
		page = d.luns[lunAddr].blocks[blockAddr].pages[pageAddr] | 
			subseqFrom[page.data, colAddr]
}

// Erase an entire block 
// A block-level operation
pred fErase [d, d' : Device, rowAddr : RowAddr] {
	let 	lunAddr = rowAddr.l, blockAddr = rowAddr.b, 
		lun' = d'.luns[lunAddr], block' = lun'.blocks[blockAddr] {
			(all page : block'.pages.elems | 
				all datum : page.data.elems | 
					datum in ErasedData) 
		
			// update the status of all pages that have been erased to "Free"
			(all addr : RowAddr |
				((addr.b = blockAddr) => d'.pageStatusMap[addr] = Free) and
				((addr.b != blockAddr) => 
					d'.pageStatusMap[addr] = d.pageStatusMap[addr]))
			
			// upgrade the erase count for the newly erased block
			let newEraseFreq = EFO/next[d.eraseFreqMap[blockAddr]],
				newReclaimBlock = blockAddr |
				LUNFrameCond[d,d', block', newEraseFreq, newReclaimBlock, rowAddr]
		}
}

/********************
 * Utility functions
 ********************/
// return the subsequence starting at from to the end of the sequence
fun subseqFrom [s : seq univ, from : Int] : seq univ {
	s.subseq[from, #s - 1]
}

/********************
 * Facts
 ********************/
fact CanonicalizeRowAddr {
	no disj r1, r2 : RowAddr | 
		r1.b = r2.b and
		r1.l = r2.l and
		r1.p = r2.p
}	

// Every page, block, and LUN belongs to some physical component
fact NoFloatingParts {
	all p : Page | some b : Block | p in b.pages[univ] //or (some l : LUN | p = l.pageRegister)
	all b : Block | some l : LUN | b in l.blocks[univ]
	all l : LUN  | some d : Device | l in d.luns[univ]
}

// TODO: blockSize * LUNSize * deviceSize
fact OneRowAddrPerPage {
	#RowAddr = mul[DEVICE_SIZE, mul[LUN_SIZE, BLOCK_SIZE]]
}

/********************
 * Test constraints
 ********************/
fun PAGE_SIZE : Int {4}
fun BLOCK_SIZE : Int {2}
fun LUN_SIZE : Int {3}
fun DEVICE_SIZE : Int {1}

/********************
 * Test runs
 ********************/
// Test erase
run {
	some d, d' : Device, rowAddr : RowAddr | fErase[d,d', rowAddr]
	some data : Data | data not in ErasedData
} for 6 but exactly 2 Device

// Test program
run {
	some d, d' : Device, colAddr : Int, rowAddr : RowAddr, readData, progData : seq Data | 
		readData = fRead[d, colAddr, rowAddr] and
		readData != progData and
		#readData = #progData and
		fProgram[d, d', colAddr, rowAddr, progData]
} for 6 but exactly 2 Device

// Test read
run {
	some d : Device, colAddr : Int, rowAddr : RowAddr, readData : seq Data | 
		readData = fRead[d, colAddr, rowAddr] and
		some data : Data | data not in ErasedData and
		some readData
} for 6 but exactly 1 Device

// Any data that read off an erased block should be non-programmed data
assert ReadErasedData{
	all d, d' : Device, rowAddr : RowAddr, colAddr : Int, readData : seq Data | 
		(fErase[d, d', rowAddr] and 
		readData = fRead[d', colAddr, rowAddr]) =>
		readData.elems in ErasedData
}

// Programming a part of the flash does not modify other parts of the flash
assert ProgramLocal {
	all d, d' : Device, colAddr1 : Int, rowAddr1 : RowAddr, progData : seq Data |
		(fProgram[d, d', colAddr1, rowAddr1, progData]) =>
		(all colAddr2 : Int - colAddr1, rowAddr2 : RowAddr - rowAddr1 |
		fRead[d, colAddr2, rowAddr2] = fRead[d', colAddr2, rowAddr2])
}

// Repeating a program operation has no effect
assert ProgramIdempotent {
	all d, d', d'' : Device,  colAddr : Int, rowAddr : RowAddr, progData : seq Data |
		(fProgram[d,d', colAddr, rowAddr, progData] and
		 fProgram[d',d'', colAddr, rowAddr, progData]) =>
		(all colAddr2 : Int, rowAddr2 : RowAddr | 
			fRead[d', colAddr2, rowAddr2] = fRead[d'', colAddr2, rowAddr2])
}

pred check1 {
	some d, d', d'' : Device,  colAddr : Int, rowAddr : RowAddr, progData : seq Data |
		(fProgram[d,d', colAddr, rowAddr, progData] and
		 fProgram[d',d'', colAddr, rowAddr, progData]) =>
		(some colAddr2 : Int, rowAddr2 : RowAddr | 
			fRead[d', colAddr2, rowAddr2] = fRead[d'', colAddr2, rowAddr2])
}


check ProgramLocal for 5 but 6 RowAddr
check ProgramIdempotent for 6 but 6 RowAddr
run check1 for 5 but 6 RowAddr

check ReadErasedData for 7 but 6 int, 8 seq
check ProgramLocal for 5 but 6 int, 8 seq
check ProgramLocal for 6 but 6 int, 8 seq
check ProgramLocal for 7 but 6 int, 8 seq
check ProgramLocal for 8 but 6 int, 8 seq
check ProgramLocal for 9 but 6 int, 8 seq
check ProgramIdempotent for 6 but 6 int, 8 seq
