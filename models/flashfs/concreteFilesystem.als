module VSR/concreteFilesystem [Data, FID]

// Alloy model of the flash filesystem, which conforms to
// the POSIX filesystem in "abstractFilesystem.als"
// Author: Eunsuk Kang, May. 2008

open VSR/flash[Data] as FD
// a sequence of intermediate states in a transaction
open util/seqrel[TranscState] as TrscSeq	

sig Inode {
	blockList : seq VBlock,
	eofIdx : Int		// last data element index in the last block of the inode
}
{
	eofIdx >= 0
	eofIdx < fsysBlockSizeParam
	not blockList.hasDups
}

// Virtual block ID
sig VBlock {}  

fun fsysBlockSizeParam : Int {FD/PAGE_SIZE}
fun fsysEraseUnitSizeParam : Int {FD/BLOCK_SIZE}

// Mapping of a virtual block to a physical address on the flash
// Note: A little pecularity in use of notations that might lead to confusion
// A virtual block in a file is NOT equal in size to a block on the flash device
// Rather, a virtual block is mapped to a page on the flash
sig ConcFsys {
//	inodeMap : FID lone -> one Inode,		// inode map
	inodeMap : FID lone -> lone Inode,
	blockMap : VBlock one -> one RowAddr
}

sig ReplTable {
	// each entry is a pair of <new_block_addr, old_block_addr>
	// where new_block_addr is the address of the block that is replacing the old block
	// in a write operation
	entries : RowAddr -> lone RowAddr
}

one sig EmptyTable in ReplTable {}
{
	no entries
}

/********************
 * File writes as transactions
 *
 * A file write opeation is a transaction that consists of a sequence of atomic 
 * flash program ops, (fProgram). To allow rollback in case of a hardware failure, 
 * we store the state of a flash device (sig Device) after each step in the transaction.
 * A typical N-step transaction looks like the following:
 * 
 * BEGIN
 * 1. fProgram #1
 * 2. fProgram #2
 * 3. erase unit reclamation
 * 4. fProgram #3
 * ....
 * N. Page status update
 * COMMIT
 * 
 * For the purpose of fault-tolerance mechanism, a set of steps from 1 to 
 * N-1 are considered Phase 1, and the last step is considered Phase 2.
 *  
 * The last operation in a transaction is always page-status update;
 * The status of every page that holds new data is changed to "Valid" 
 * (validatePage) and
 * the status of every page that holds old data is changed to "Invalid." 
 * (invalidatePage)
 *
 * Thus, each transaction is represented by a sequence of ProgramState atoms and
 * an ValidatedState atom as the final state in transaction.
 * 
 * At the time of a commit, two pieces of information must be
 * updated at the filesystem level (i.e. level visible to the filesystem client): 
 * (1) virtual-block to page-addr mapping must be updated to map a modified
 * file block to a page that contains valid, fresh data
 * (2) If a write operation adds one or more blocks to a file, then blockList
 * in Inode must also be updated.
 *
 * To enable the update in (1), a list of <new, old> block pairs is accumulated 
 * throughout the steps in a transaction using ReplTable (in ProgramState).
 * A ProgramState also accumulates a list of new blocks (newBlockSeq) 
 * to enable the update in (2). 
 *
 ********************/
// An intermediate state after each operation in a transaction
abstract sig TranscState {
	dev : Device
}

sig ProgramState extends TranscState {
	programTbl : ReplTable,    
	reclaimTbl : ReplTable, 		// <new, old> block pairs during an erase-unit reclamation
	newBlockSeq : seq RowAddr
}

sig ValidatedState extends TranscState {}

// A sequence of transactional states
sig StateSeqFactory {
	stateSeq : TrscSeq/SeqIdx -> TranscState
}
{
	TrscSeq/isSeq[stateSeq]
}

/**********************************************
 * Frame conditions  & other auxiliary functions *
 **********************************************/
pred cfsysPromote[fid : FID, inode, inode' : Inode, cfsys, cfsys' : ConcFsys]{
	inode = cfsys.inodeMap[fid] and
	cfsys'.inodeMap = cfsys.inodeMap ++ (fid -> inode')
}

fun findRowAddr[cfsys : ConcFsys, inode : Inode, blockIdx : Int] : RowAddr  {
	cfsys.blockMap[inode.blockList[blockIdx]]
}

// returns one block full of ErasedData
fun fillData : seq ErasedData {
	{i : Int, e : ErasedData | i >= 0 and i < fsysBlockSizeParam}
}

// returns a sequence of ErasedData elements of a specified length
fun fillDataBlocksOfLength[length : Int] : seq ErasedData {
	{i : Int, e : ErasedData | i >= 0 and i < mul[fsysBlockSizeParam,length]}
}

// an empty sequence (i.e. sequence of length 0)
fun emptyData : seq ErasedData {
	{i : Int, e : ErasedData | i >= 0 and i < 0}
}

// Convert a RowAddr sequence index into an index for an intermediate transc. state
fun pseq2TrscSeq[pseq : FD/PSeq/SeqIdx] : TrscSeq/SeqIdx {
	{s : TrscSeq/SeqIdx |
		#TrscSeq/ord/prevs[s] = 
		#FD/PSeq/ord/prevs[pseq]}
}

// Convert a FsystemState sequence into a RowAddr sequence
fun trscSeq2Int[trscSeq: TrscSeq/SeqIdx] : Int {
	#TrscSeq/ord/prevs[trscSeq]
}

// return the row address at the specified page sequence
fun rowAddrAt[rowAddrs : set RowAddr, pseq_idx : FD/PSeq/SeqIdx]: RowAddr {
	{addr : rowAddrs | addr.p = pseq_idx}
}

/*******************************
 * Fault-tolereance related signatures *
 *******************************/
abstract sig OpResult {}

one sig Succ extends OpResult {}

// Crash data after Phase 1 failure
sig Fail1 extends OpResult {
	reclTbl : ReplTable
}

// Crash data after Phase 2 failure
sig Fail2 extends OpResult {
	programTbl : ReplTable,
	reclaimTbl : ReplTable,
	newBlockSeq : seq RowAddr,
	fileID : FID,
	EOFIdx : Int
}

/********************************
 * Read operation *
 ********************************/
// preconditions on the input arguments to a read operation
pred readPreconds[inode : Inode, offset, size, lastBlockIdx, lastPageIdx : Int] {

	let blockSize = fsysBlockSizeParam,
		 curBlocks = inode.blockList,
		 eofIdx = inode.eofIdx,

		// maxReadLength: max. number of bytes that can be read from the file
		// i.e. the number of data elements in the current file
		// maxReadLength = blockSize*(#curbBlocks - 1) + (eofIdx + 1)
		maxReadLength = add[mul[blockSize, sub[#curBlocks, 1]], add[eofIdx, 1]]  {

			// offset must be valid
			offset >= 0
			offset < maxReadLength
			// size cannot exceed the max. # of data elements that can be read
			size >= 0
			size <= sub[maxReadLength, offset]
			lastBlockIdx < #curBlocks
	
			// Cannot read beyond the end of file index 
			(lastBlockIdx = curBlocks.lastIdx) => lastPageIdx <= eofIdx
	}

}

// Read the first block in the file 
// This is considered a special case from reading other blocks since
// the offset may not be a multiple of block size
pred readFirstBlock [cfsys : ConcFsys, d : Device, firstBlock : VBlock,
						offset : Int, buffer : seq Data] {
	let rowAddr = cfsys.blockMap[firstBlock] |
		 buffer = fRead[d, offset, rowAddr]
}

pred readRemainingBlocks[cfsys : ConcFsys, d : Device, blocks : seq VBlock,  
							readStopIdx : Int, buffer : seq Data]{
    let blockSize = fsysBlockSizeParam |
	// each instance of unfolding of the universal quantifier
	// corresponds to reading one block
    (all idx : blocks.inds |
     let vblock = blocks[idx],
         rowAddr = cfsys.blockMap[vblock],
		  // blockSize = size of a virtual block = size of  a flash page = PAGE_SIZE
         from = mul[blockSize, idx],					// from = blockSize * idx
         to = sub[add[from,blockSize], 1] |		// to = from + blockSize - 1
         ((idx = blocks.lastIdx) =>
				 /*
				 Special case:                                                                                                                 
				 When reading the last block, must stop at readStopIdx                                                                       
				 */
            buffer.subseqFrom[from] =
                fRead[d, 0, rowAddr].subseq[0,readStopIdx]
         else
            buffer.subseq[from,to] = fRead[d, 0, rowAddr]))
}

// Client-level entry for the read operation
// Read "size" number of data elements from the inode indicated by "fid" starting at
// the "offset".  The output data is fsysd in "buffer".
// TODO: Tighter constraints than in the POSIX requirements: always returns data sequence
// 			of length "size", rather than that of length UP TO "size" - else, fails for all other
//				input arguments
pred readConc [cfsys: ConcFsys, d : Device, fid : FID, 
					  offset, size : Int, buffer : seq Data] {
	let blockSize = fsysBlockSizeParam,
		 inode = cfsys.inodeMap[fid], 
		 blockList = inode.blockList,

		// blockIdx1: index of the starting block 
		// pageIdx1: index of the byte in the starting block
		// blockIdx2: index of the last block to read
		// pageIdx2 : index of the byte in the last block		
		blockIdx1 = div[offset, blockSize],
		pageIdx1 = rem[offset, blockSize],
		// offset of the last data element to be read = offset + size - 1
		endingOffset = sub[add[offset, size], 1],
		blockIdx2 = div[endingOffset, blockSize],
		pageIdx2 = rem[endingOffset, blockSize], 
		firstBlockSize = sub[blockSize, pageIdx1],   
		readBlockSeq = blockList.subseq[blockIdx1, blockIdx2] {
	
			// input arguments must satisfy the preconditions for a read operation
			readPreconds[inode, offset, size, blockIdx2, pageIdx2]

			(#readBlockSeq = 1) => { 	// single block: special case
				let rowAddr = cfsys.blockMap[readBlockSeq.elems] | 
					buffer = fRead[d, pageIdx1, rowAddr].subseq[0, sub[pageIdx2, pageIdx1]]
			} else {
				readFirstBlock[cfsys, d, readBlockSeq.first, pageIdx1, 
								 buffer.subseq[0, sub[firstBlockSize, 1]]]
				readRemainingBlocks[cfsys, d, readBlockSeq.rest, pageIdx2, 
										 buffer.subseqFrom[firstBlockSize]]
			}
		}
}

/***********************************
 * Erase-unit reclamation related *
 * These predicates/functions are "invoked" during a write operation
 * when no free block is available for new data
 * Thus, here we are following "on-demand" garbage collection model
 ***********************************/
pred eraseDirtyUnit[curState, nextState : TranscState, dirtyUnit : FD/BSeq/SeqIdx] {
	some rowAddr : RowAddr |
	let d = curState.dev, d' = nextState.dev,
		progTbl = curState.programTbl, progTbl' = nextState.programTbl,
		reclTbl = curState.reclaimTbl, reclTbl' = nextState.reclaimTbl, 
		newBlockList = curState.newBlockSeq, newBlockList' = nextState.newBlockSeq {
			rowAddr.b = dirtyUnit
			fErase[d, d', rowAddr]
			progTbl' = progTbl
			reclTbl' = reclTbl
			newBlockList' = newBlockList
	}
}

// Backup a single valid block by copying them (i.e. programming) into a reserve block
pred backupSingleBlock[curState, nextState : TranscState, srcAddr, destAddr : RowAddr] {
	let d = curState.dev, d' = nextState.dev,
		progTbl = curState.programTbl, progTbl' = nextState.programTbl,
		reclTbl = curState.reclaimTbl, reclTbl' = nextState.reclaimTbl, 
		newBlockList = curState.newBlockSeq, newBlockList' = nextState.newBlockSeq,
		sourceData = fRead[d, 0, srcAddr] {

			// program the flash
			fProgram[d, d', 0, destAddr, sourceData]

			// fsys the <new, old> replacement page pair into the reclamation table
			reclTbl'.entries = reclTbl.entries ++ (destAddr -> srcAddr)
			progTbl' = progTbl
			newBlockList' = newBlockList
		}
}

// Copy all valid blocks from source unit to the reclaim unit
// i.e. for some i_th valid file block P_i in a dirty erase unit, program the data in P_i into
// the corresponding i_th file block in the reserve unit, P'_i. 
pred backupValidBlocks[stateSeq : TrscSeq/SeqIdx -> ProgramState, 
										dirtyUnit : FD/BSeq/SeqIdx] {
	let firstDev = stateSeq.first.dev, 
		srcAddrs = {r1 : RowAddr | r1.b = dirtyUnit}, 
		destAddrs = {r2 : RowAddr | r2.b = firstDev.reserveBlock} {

		// the length of the sequence = #blocks to backup
		#stateSeq = add[fsysEraseUnitSizeParam, 1]

		// quantified var: page address in the flash erase unit
		// ranges from 0 to (eraseUnitSizeParam - 1)
		// each unfolding instance of the quantifier corresponds to
		// backing up a single block
		(all pseq_idx : srcAddrs.p |
			let trscSeq_idx = pseq2TrscSeq[pseq_idx], 
				curState = stateSeq[trscSeq_idx],
				nextState = stateSeq[trscSeq_idx.next],
				curSrcAddr = srcAddrs.rowAddrAt[pseq_idx], 
				curDestAddr = destAddrs.rowAddrAt[pseq_idx] |
	
				(firstDev.pageStatusMap[curSrcAddr] = Valid) => {
					// The block at this addr must be backed up on a reclaim unit
					// Copy this block on the source unit to the corresponding position
					// on the destination unit
					backupSingleBlock[curState, nextState, curSrcAddr, curDestAddr]
				} else {
					// the page at this address is either free or invalid (i.e. can be erased)
					nextState = curState
				}
		)
	}

}

// The main entry function for erase-unit reclamation
pred performEraseReclamation[initState, finalState : TranscState] {

	// an erase-unit reclamation itself is a transaction, consisting of
	// a sequence of flash program operations followed by page status update
	some stateSeqFactory : StateSeqFactory, dirtyUnit : FD/BSeq/SeqIdx | 
	let stateSeq = stateSeqFactory.stateSeq, 
		// sequence of states after each backup operation
		backupStateSeq = stateSeq.butlast.butlast,
		// state after the page status update
		validatedState = stateSeq.butlast.last,
		erasedState = stateSeq.last {
		
			stateSeq.first = initState
			stateSeq.last = finalState
		
			/* Erase-unit reclamation is a 4-step process */

			//1. Select some dirty unit with the least erasure frequency
			dirtyUnit in selectLeastErasedUnit[initState.dev]

			//2. Backup all of the valid blocks in the erase unit onto the reserve unit
			//TODO : Introduce failure here?
			backupValidBlocks[backupStateSeq, dirtyUnit]

			//3. Validate all of the blocks that were backed-up
            // and invalidate the old, obsolete blocks
			//TODO : Introduce failure here?
			updatePageStatuses_succ[backupStateSeq.last, validatedState]
	
			//4. Finally, after the backup is done, erase the selected dirty unit
			eraseDirtyUnit[validatedState, erasedState, dirtyUnit]
		}

}

/********************************
 * Write operation *
 ********************************/
// Initial constraints on a sequence of intermediate states in a transaction
pred stateSeqConds[stateSeq : TrscSeq/SeqIdx -> TranscState, length : Int] {

	#stateSeq = length

	stateSeq.elems in ProgramState

	// the initial program table is empty	
	stateSeq.first.programTbl = EmptyTable
	stateSeq.first.reclaimTbl = EmptyTable

	// the potential sequence of new inode blocks is initially empty
	stateSeq.first.newBlockSeq.isEmpty

}

// After all of data have been successfully programmed to the flash,
// validate all flash pages with new data, and invalidate every page that
// holds obsolete file data.
// This is done by updating pageStatusMap in sig Device (flash.als)
// Success case
pred updatePageStatuses_succ[curState : ProgramState, nextState : ValidatedState] {
 
	let d = curState.dev, d' = nextState.dev,
		progTbl = curState.programTbl,
		newBlockSeq = curState.newBlockSeq,
		oldRowAddrs = univ.(progTbl.entries),
		newRowAddrs = progTbl.entries.univ + newBlockSeq.elems {
			
			// invalidate the old pages
			(all oldRowAddr : oldRowAddrs | invalidatePage[d, d', oldRowAddr])

			// validate the newly programmed pages
			(all newRowAddr : newRowAddrs | validatePage[d, d', newRowAddr])

			// necessary frame condition
			// the status flags for all other pages remain the same
			(all remainder : RowAddr - (oldRowAddrs + newRowAddrs) |
				fixPage[d, d', remainder])
			
			// another frame condition
			// erase frequencies for the flash erase units do not change
			fixEraseFrequencies[d, d']
		}

}

// Failure case of updatePageStatuses
pred updatePageStatuses_fail[curState : ProgramState, nextState : ValidatedState] {

	// Simple failure model
	// Assume that failure occurs during the invalidation process
	// More specificially, the flash H/W fails after invalidating a subset of old blocks
	let d = curState.dev, d' = nextState.dev,
		progTbl = curState.programTbl,
		oldRowAddrs = univ.(progTbl.entries) |
		some failureAddr : oldRowAddrs {
			(all rowAddr : oldRowAddrs - failureAddr | invalidatePage[d, d', rowAddr])
			(all remainder : RowAddr - (oldRowAddrs - failureAddr) | fixPage[d, d', remainder])
			fixEraseFrequencies[d, d']
	}
	
}

// Commit the changes made during the write operation by updating
// the page status mapping and the list of inode blocks
pred updateFsysInfo[cfsys, cfsys' : ConcFsys, fid : FID, 
					progTbl, reclTbl : ReplTable, newBlockList : seq RowAddr,
					newEOFIdx : Int] {

	let mergedEntries = progTbl.entries + reclTbl.entries |

	// First, update the virtual-to-physical mapping in cfsys from the program table
	// Also, some of the valid pages may have been moved around during reclamation
	// process - update the mapping for these pages, too
	(all newBlockAddr : mergedEntries.univ |
		let oldBlockAddr = mergedEntries[newBlockAddr],
			oldVBlock = cfsys.blockMap.oldBlockAddr,
			newVBlock = cfsys.blockMap.newBlockAddr {
				cfsys'.blockMap[oldVBlock] = newBlockAddr 
				cfsys'.blockMap[newVBlock] = oldBlockAddr
			}
	) and

	// Frame condition: Only the entries that appear in the program table affect  
	//					   the virtual-to-physical mapping
	(all unchangedBlockAddr : RowAddr - (mergedEntries.univ + univ.mergedEntries) |
		cfsys'.blockMap.unchangedBlockAddr = cfsys.blockMap.unchangedBlockAddr
	) and

	// update the inode information by appending the list of new blocks to inode.blockList
	// TODO: simplified from the previous version
	(let inode = cfsys.inodeMap[fid], inode' = cfsys'.inodeMap[fid],  
		newBlockSeq = {i : Int, vb : VBlock | vb = cfsys'.blockMap.(newBlockList[i])} |
		inode'.blockList = inode.blockList.append[newBlockSeq]
	) and

	// set the end of file index
	(let inode' = cfsys'.inodeMap[fid] | inode'.eofIdx = newEOFIdx)
	
}

// Program one block worth of data into a flash page by invoking
// the flash API function fProgram
// Two cases:
// 1) Modifying an existing part of the file - add a <new,old> block pair to
//		the list of accumulated pairs (progTbl in sig ProgramState)
// 2) Appending data to the file (i.e. allocate a new block) - add the address
//		of the new block to the accumulated list (newBlockList in sig ProgramState)  
pred programIntoFreeBlock[curState, nextState : TranscState,
								oldBlockAddr : RowAddr, writeData : seq Data] {
	let d = curState.dev, d' = nextState.dev,
		progTbl = curState.programTbl, progTbl' = nextState.programTbl,
		reclTbl = curState.reclaimTbl, reclTbl' = nextState.reclaimTbl, 
		newBlockList = curState.newBlockSeq, newBlockList' = nextState.newBlockSeq |
		some newBlockAddr : searchFreeBlocks[d] {

			// program the flash
			fProgram[d, d', 0, newBlockAddr, writeData]

			// Modifying an existing block in an inode?
			(some oldBlockAddr) => {
				progTbl'.entries = progTbl.entries ++ (newBlockAddr -> oldBlockAddr)
				newBlockList' = newBlockList
				reclTbl' = reclTbl
			} 

			// Adding a new block to the inode?
			(no oldBlockAddr) => {
				progTbl' = progTbl
				newBlockList' = newBlockList.add[newBlockAddr]
				reclTbl' = reclTbl
			}
		}

}

// return the set of addresses for all free pages, 
// except the ones that are reserved for reclamation
fun searchFreeBlocks[d : Device] : set RowAddr {
	let reclaimPages = {r : RowAddr | r.b = d.reserveBlock} |
		d.pageStatusMap.Free - reclaimPages
}

fun searchInvalidBlocks[d : Device] : set RowAddr {
	d.pageStatusMap.Invalid
}

// If there is a free block, then program the input data into that block
// If no free block is available, then reclaim an obsolete block to free up space for new data
pred programVBlock[curState, nextState : TranscState,
						 oldBlockAddr : RowAddr, writeData : seq Data] {

	let freeBlockAddrs = searchFreeBlocks[curState.dev] {
		(some freeBlockAddrs) => {
			programIntoFreeBlock[curState, nextState, oldBlockAddr, writeData]	
		} else {
			some interState : TranscState {
				performEraseReclamation[curState, interState]
				programIntoFreeBlock[interState, nextState, oldBlockAddr, writeData]
			}
		}
	}

}

// Some of the valid pages may have been moved around during reclamation
// process - apply the entries in the reclaim replacement tables to 
// the VBlock to RowAddr mapping
fun findCorrectBlockAddr [cfsys : ConcFsys, blockID : VBlock, 
							  	 sysState : TranscState] : RowAddr {
	let oldBlockAddr = cfsys.blockMap[blockID],
		migratedBlockAddr = sysState.reclaimTbl.entries.oldBlockAddr |
		(some migratedBlockAddr) => migratedBlockAddr 
		else oldBlockAddr
}

// Given a write data buffer, a starting block index, and # blocks to program,
// each iteration of programLoop invokes programBlock, which, in turn, calls 
// fProgram to program a fragment of input data into a corresponding page on the flash. 
pred programLoop[cfsys : ConcFsys, inode : Inode,
								stateSeq : TrscSeq/SeqIdx -> ProgramState,
							 	 writeData : seq Data, startBlockIdx, numBlocksToProgram : Int] {
	 
		let blockSize = fsysBlockSizeParam {
		
				// the length of the state sequence in the write operation:
				// (number of blocks to program) + 1 
				stateSeqConds[stateSeq, add[numBlocksToProgram, 1]] 
		
				// each unfolding instance of the quantifier corresponds to
				// one program operation
				(all trscSeq_idx : stateSeq.butlast.inds |
				let idx = trscSeq2Int[trscSeq_idx],
					preState = stateSeq[trscSeq_idx],			
					postState = stateSeq[trscSeq_idx.next],
					from = mul[blockSize, idx],							// from = blockSize * idx
					to = sub[add[from, blockSize], 1],					// to = from + (blockSize - 1)
					dataFragment = writeData.subseq[from, to],	// current fragment of input data
					curBlockIdx = add[startBlockIdx, idx],			// index of the block in the inode
					vblock = inode.blockList[curBlockIdx],			// virtual ID of the block
					rowAddr = findCorrectBlockAddr[cfsys, vblock, preState] |
						programVBlock[preState, postState, rowAddr, dataFragment]
				)

		}	
}

// Phase 1 of the file write operation
// A sequence of atomic write operations
// Success case: All blocks are properly programmed
pred programBlocks_succ [cfsys : ConcFsys, fid : FID, 
							  				stateSeq : TrscSeq/SeqIdx -> ProgramState,
							  				writeData : seq Data, blockIdx1, blockIdx2 : Int] {
			
 	let numBlocksToProgram = add[sub[blockIdx2, blockIdx1], 1],
		inode = cfsys.inodeMap[fid] {
			programLoop[cfsys, inode, stateSeq, writeData, blockIdx1, numBlocksToProgram]
	}

}

// Phase 1 of the file write operation
// A sequence of atomic write operations
// Failure case: Power loss in the flash after some number of blocks (failureBlockIdx)
pred programBlocks_fail [cfsys : ConcFsys, fid : FID, 
							stateSeq : TrscSeq/SeqIdx -> ProgramState,
							writeData : seq Data, blockIdx1, blockIdx2 : Int] {	
 
	some failureBlockIdx : Int {
	
		failureBlockIdx > blockIdx1 
		failureBlockIdx <= blockIdx2
		
		let numBlocksToProgram = sub[failureBlockIdx, blockIdx1],
			inode = cfsys.inodeMap[fid] {		
				programLoop[cfsys, inode, stateSeq, writeData, blockIdx1, numBlocksToProgram]
		}
	}

}

// Simulate a hardware failure during Phase 1
// i.e. power loss in the middle of program operations
pred phaseOneCrash[cfsys, cfsys' : ConcFsys, fid : FID, 
						  stateSeq : TrscSeq/SeqIdx -> TranscState,
						  writeData : seq Data, blockIdx1, blockIdx2: Int] {
	
	let programStateSeq = stateSeq.butlast,
		validatedState = stateSeq.last,
		finalProgState = programStateSeq.last,
		interDev = finalProgState.dev {
			// h/w fails after programming only a subset of specified blocks
			programBlocks_fail [cfsys, fid, programStateSeq, 
										   writeData, blockIdx1, blockIdx2]
			validatedState.dev = interDev
		}

	// the file system does not change, only the state of flash device changes
	cfsys' = cfsys

}	

// Simulate a hardware failure during Phase 2
// i.e. powerloss while updating the page status
pred phaseTwoCrash[cfsys, cfsys' : ConcFsys, fid : FID, 
						  stateSeq : TrscSeq/SeqIdx -> TranscState,
						  writeData : seq Data, blockIdx1, blockIdx2: Int] {
	
	let programStateSeq = stateSeq.butlast,
		validatedState = stateSeq.last {
		
		// All of the blocks are sucessfully programmed
		programBlocks_succ[cfsys, fid, programStateSeq, 
									    writeData, blockIdx1, blockIdx2]
	
		// But h/w fails while validating the newly written pages in the flash
		updatePageStatuses_fail[programStateSeq.last, validatedState]	
	}

	// the filefsys does not change
	cfsys' = cfsys

}

// Both Phase 1 and Phase 2 of the file write operation succeed
pred writeSuccess[cfsys, cfsys' : ConcFsys, fid : FID, 
					   stateSeq : TrscSeq/SeqIdx -> TranscState,
					   writeData : seq Data, blockIdx1, blockIdx2, newEOFIdx : Int] {

	let programStateSeq = stateSeq.butlast,
		finalProgState = programStateSeq.last,
		validatedState = stateSeq.last {

		// program all of the blocks between blockIdx1 and blockIdx2
		programBlocks_succ[cfsys, fid, programStateSeq, 
							    writeData, blockIdx1, blockIdx2]

		// validate the newly written pages in the flash and
		// invalidae old pages
		updatePageStatuses_succ[finalProgState, validatedState]

		(let finalProgTbl = finalProgState.programTbl,
			 finalReclTbl = finalProgState.reclaimTbl,
			 newBlockSeq = finalProgState.newBlockSeq |
			 
			// Filesystem-level operation
			// Commit the changes done by the operation
			// by updating the block mapping and inode information in the filefsys
			updateFsysInfo[cfsys, cfsys', fid, 
									finalProgTbl, finalReclTbl,
									newBlockSeq, newEOFIdx]
		)
	}

}

pred dumpPhase1CrashInfo[failureInfo : Fail1, crashState : ProgramState] {	
	failureInfo.reclTbl = crashState.reclaimTbl
}

pred dumpPhase2CrashInfo[failureInfo : Fail2, crashState : ProgramState, fid : FID, 
											newEOFIdx : Int] {
	failureInfo.programTbl = crashState.programTbl
	failureInfo.reclaimTbl = crashState.reclaimTbl
	failureInfo.newBlockSeq = crashState.newBlockSeq	
	failureInfo.fileID = fid and
	failureInfo.EOFIdx = newEOFIdx
}

// Write operation cases
// Non-deterministically chooses between three different cases to simulate
// possible hardware failures
// Case 1. Failure during Phase 1
// 		2. Failure during Phase 2
// 		3. Success case
//
// blockIdx1 : Idx of the first inode block to be modified by write operation
// blockIdx2 : Idx of the last block to be modified by write operation
pred writeOpCases[cfsys, cfsys' : ConcFsys, fid : FID, d, d' : Device, 
					    	writeData : seq Data, blockIdx1, blockIdx2, newEOFIdx: Int,
					   	 	opResult : OpResult] {
	// "Instantiate" a sequence of TranscState atoms, each of which represents
	// the state of the flash device after each operation in a transaction
	some stateSeqFactory : StateSeqFactory |
	let stateSeq = stateSeqFactory.stateSeq |
		stateSeq.first.dev = d and
		stateSeq.last.dev = d' and
		stateSeq.last in ValidatedState and 
		let finalProgState = stateSeq.butlast.last {
		
		/* Flash-level operations - 2 main phases */

		/* 
			Phase 1:
				1.1 Program the input data into free, available blocks,
					reclaiming obsolete blocks, if necessary.
				1.2 Set the status of each modified page to "Allocated"

			Phase 2:
				2.1 Invalidate the old data by setting the status of the	
					 corresponding pages to "Invalid"
				2.2 Validate the new data by setting the status of the
					modified pages to "Valid"
		 */

		/* 
			Fault-torelance model
			The flash H/W may crash due to power-loss at any point in Phase 1 or Phase 2
		 */
		
		// Phase 1 crash
		(phaseOneCrash[cfsys, cfsys', fid, stateSeq, 
								 writeData, blockIdx1, blockIdx2] and
		 // save a snapshot of the transactional state before crashing
		 dumpPhase1CrashInfo[opResult, finalProgState]) 

		or

		// Phase 2 crash
		(phaseTwoCrash[cfsys, cfsys', fid, stateSeq,  
								 writeData, blockIdx1, blockIdx2] and
		 // save a snapshot of the transactional state before crashing 
		 dumpPhase2CrashInfo[opResult, finalProgState, fid, newEOFIdx])
		
		or 

		// Write success
		(writeSuccess[cfsys, cfsys', fid, stateSeq,  
							 writeData, blockIdx1, blockIdx2, newEOFIdx] and
		 opResult = Succ)
	} 
}

// Set of conditions that should hold for input arguments 
pred writePreconds[d : Device, numNewBlocks, offset,size, bufferSize : Int] {
	//Cond1 : Offset must be valid
	offset >= 0

	//Cond2 : Size must be valid
	size >= 0
	size <= bufferSize
	
	// Cond2 : cfsys has enough free blocks to write input data starting at given offset
	let numRequiredBlocks = numNewBlocks, 
		numAvailableBlocks = #searchFreeBlocks[d]  + #searchInvalidBlocks[d] |
		numRequiredBlocks <= numAvailableBlocks
}

// Pad the input data buffer so that the size of the padded buffer is a multiple
// of blockSize - this makes flash programming much easier to do
// An input buffer can be padded in three different places
// 1. If the offset in the first block (i.e. pageIdx1) is not at the beginning of the block,
//		then pad the front of the buffer with fill data (prefixData)
// 2. If the offset in the last block (i.e. pageIdx2) is not at the end of the block,
// 	then pad the end of the buffer with fill data (suffixData)
// 3. If blockIdx1 (starting block) is not an existing file block (i.e. appending only new
// 	blocks to the file), then the space between the last existing file block and blockIdx1
// 	must be filled with erased data (prefixBlockData)
fun padInputData[cfsys : ConcFsys, fid : FID, d : Device, inputData : seq Data, 
					  		blockIdx1, blockIdx2, pageIdx1, pageIdx2 : Int] : seq Data {
	let 	inode = cfsys.inodeMap[fid],
		curNumBlocks = #inode.blockList,
		rowAddr1 = findRowAddr[cfsys, inode, blockIdx1],
		rowAddr2 = findRowAddr[cfsys, inode, blockIdx2],
		prefixData = 
			// Is the first block to be written an existing block?
			// If so, the prefix must be filled with existing file data 
			// (by reading directly from the flash)
			((blockIdx1 < curNumBlocks) => {
				fRead[d, 0, rowAddr1].subseq[0, sub[pageIdx1, 1]]
			} else {
				// Fill the positions prior to pageIdx1 in the first block with erased data
				fillData.subseq[0, sub[pageIdx1, 1]]
			}),
		suffixData =
			// Is the last block to be written an existing block?
			// If so, the suffix must be filled with existing file data 
			// (by reading directly from the flash)
			((blockIdx2 < curNumBlocks) => {
				fRead[d, add[pageIdx2, 1], rowAddr2]
			} else {
				// Fill the remaining positions in the last block with erased data
				fillData.subseq[0, sub[pageIdx1, 1]]
			}),
		prefixBlockData = 
			((blockIdx1 > curNumBlocks) => {
				fillDataBlocksOfLength[sub[blockIdx1, curNumBlocks]]
			} else {
				emptyData
			}) |
		// the resulting padded data
		prefixBlockData.append[prefixData.append[inputData.append[suffixData]]]
}

// After input buffer has been padded with suffix data, the starting block index
// must be adjusted accordingly 
// More specifically, if blockIdx1 is greater than the current number of blocks in the file,
// it must have been paded with some number of blocks of erased data
// Then, the write operation must begin at the block immediately following the last block
// in the file  
fun calculateNewStartBlockIdx[cfsys : ConcFsys, fid : FID, blockIdx1 : Int] : Int {
	let inode = cfsys.inodeMap[fid] |
		(blockIdx1 > #inode.blockList) => #inode.blockList 
		else blockIdx1
}

// Set the end of file (eof) index for the last block in the modified inode
fun calcEOFIdx[cfsys : ConcFsys, fid : FID, blockIdx2, pageIdx2 : Int] : Int {
	let inode = cfsys.inodeMap[fid],
		lastBlockIdx = inode.blockList.lastIdx |
		((no lastBlockIdx) || 
		 (lastBlockIdx < blockIdx2) || 
		 (lastBlockIdx = blockIdx2 and inode.eofIdx < pageIdx2)) => 
			pageIdx2 
		else 
			// the operation modifies only existing data - EOF index does not change
			inode.eofIdx
}

// Client-level entry for the write operation
pred writeConc[cfsys, cfsys' : ConcFsys, d, d' : Device, fid : FID,
						originBuffer : seq Data, offset, size : Int, opResult : OpResult] {

	let blockSize = fsysBlockSizeParam,
		buffer = originBuffer.subseq[0, sub[size, 1]],
		blockIdx1 = div[offset, blockSize],		// starting block index
		pageIdx1 = rem[offset, blockSize],		// offset in the starting block
		endingOffset = sub[add[offset, #buffer], 1],	
		blockIdx2 = div[endingOffset, blockSize],		// ending block index
		pageIdx2 = rem[endingOffset, blockSize], 	// offset within the ending block
		// numBlocksToProgram = blockIdx2 - blockIdx1 + 1
		numBlocksToProgram = add[sub[blockIdx2, blockIdx1], 1],
		inode = cfsys.inodeMap[fid], inode' = cfsys'.inodeMap[fid] |

		// must satisfy the preconditions for a write operation
		writePreconds[d, numBlocksToProgram, offset, size, #buffer] and

		// precondition on fid - file must exist
		some inode and

		// frame conditions - this operation modifies only one file
		cfsysPromote[fid, inode, inode', cfsys, cfsys'] and

		((#buffer = 0) => {
			// On empty input, do nothing
			cfsys = cfsys' and d = d'
		} else {
			let // pad the input data 
				paddedData = padInputData[cfsys, fid, d, buffer, blockIdx1, blockIdx2,
												   				pageIdx1, pageIdx2],
				// calculate the new starting block index (after padding)
				blockIdx1' = calculateNewStartBlockIdx[cfsys, fid, blockIdx1],
				// calculate the new end of file index
				newEOFIdx = calcEOFIdx[cfsys, fid, blockIdx2, pageIdx2] |
				//  perform the write operation
				writeOpCases[cfsys, cfsys', fid, d, d', paddedData, 
										blockIdx1', blockIdx2, newEOFIdx,
										opResult]
		})

}

/********************************
 * Flash filesystem recovery *
 ********************************/
/*
 * Recovering from power-loss in the Phase One of Write operation
 * At this point, some of the pages have been programmed and upgraded to
 * the status "Allocated." 
 * In addition, some of the valid pages may have been moved around during reclamation
 * process.
 * We revert back to the original state (i.e. state at the beginning of the write
 * operation) by invalidating all of the allocated pages, and if necessary,
 * updating the VBlock_to_RowAddr map in the filefsys.
 */
pred recoverFromPhaseOneCrash[cfsys, cfsys' : ConcFsys, d, d' : Device,
										failureInfo : Fail1] {
	
	let allocatedPageAddrs = d.pageStatusMap.Allocated {
		// Invalidate the allocated pages
		(all allocatedPageAddr : allocatedPageAddrs |
			invalidatePage[d, d', allocatedPageAddr]) 

		// Fix all other pages
		(all otherPageAddr : RowAddr - allocatedPageAddrs |
			fixPage[d, d', otherPageAddr])

		// fix the erase frequency for each block
		fixEraseFrequencies[d, d']
	}
	
	// update the mapping for valid pages that have been moved during
	// the reclamation process
	let reclTbl = failureInfo.reclTbl {
		(all newBlockAddr : reclTbl.entries.univ |
			let oldBlockAddr = reclTbl.entries[newBlockAddr],
				oldVBlock = cfsys.blockMap.oldBlockAddr,
				newVBlock = cfsys.blockMap.newBlockAddr {
					cfsys'.blockMap[oldVBlock] = newBlockAddr 
					cfsys'.blockMap[newVBlock] = oldBlockAddr
				}
		)

		// Frame condition: Only the entries that appear in the program table affect  
		//					   the virtual-to-physical mapping
		(all unchangedBlockAddr : RowAddr - (reclTbl.entries.univ + univ.(reclTbl.entries)) |
			cfsys'.blockMap.unchangedBlockAddr = cfsys.blockMap.unchangedBlockAddr
		)
	}

}

/*
 * Recovering from power-loss in the Phase Two
 * At this point, all of the pages have been programmed and upgraded to
 * the status "Allocated." 
 * Some of the old pages have been invalidated, but not all.
 * We revert back to the next state (i.e. state at the end of the write
 * operation) by invalidating all of the old pages, and by validating newly
 * programmed pages
 */
pred recoverFromPhaseTwoCrash[cfsys, cfsys' : ConcFsys, d, d' : Device,
										failureInfo: Fail2] {
	let finalProgTbl = failureInfo.programTbl,
		finalReclTbl = failureInfo.reclaimTbl,
		newBlockSeq = failureInfo.newBlockSeq,
		fid = failureInfo.fileID,
		newEOFIdx = failureInfo.EOFIdx,
		oldRowAddrs = univ.(finalProgTbl.entries),
		allocatedPageAddrs = d.pageStatusMap.Allocated {
			// Invalidate old pages
			(all oldRowAddr : oldRowAddrs |
				invalidatePage[d, d', oldRowAddr])
		
			// Validate the allocated (i.e. newly programmed) pages
			(all allocatedPageAddr : allocatedPageAddrs |
				validatePage[d, d', allocatedPageAddr])

			// Fix all other pages
			(all otherPageAddr : RowAddr - (oldRowAddrs + allocatedPageAddrs) |
				fixPage[d, d', otherPageAddr])
	
			// Erase frequencies for all flash erase units do not change
			fixEraseFrequencies[d, d']

			// update the block mapping information in the filefsys
			updateFsysInfo[cfsys, cfsys', fid, 
							finalProgTbl, finalReclTbl, 
							newBlockSeq, newEOFIdx] 
	}
}

pred recoverFromPowerLoss[cfsys, cfsys' : ConcFsys, d, d' : Device, 
									lastOpResult : OpResult] {
	(lastOpResult = Fail1) => recoverFromPhaseOneCrash[cfsys, cfsys', d, d', lastOpResult]
	(lastOpResult in Fail2) => recoverFromPhaseTwoCrash[cfsys, cfsys', d, d', lastOpResult]
	// Don't do anything
	(lastOpResult = Succ) => (cfsys' = cfsys and d' = d) 
}

/********************
 * Facts
 ********************/
fact FileBlocksAreDisjoint {
	all c : ConcFsys | all disj i1, i2 : FID.(c.inodeMap) |
		no (i1.blockList.elems & i2.blockList.elems)
}

/********************
 * Concrete state invariants
 ********************/
// empty files have 0 as the EOF index
pred eofReset[cfsys : ConcFsys] {
	all inode : Inode |
		no inode.blockList => inode.eofIdx = 0
}

// All data elements after the End-Of-File index are erased
pred eofDataErased [cfsys : ConcFsys, d : Device] {
	all fid : FID | 
		let inode = cfsys.inodeMap[fid],
			eofIdx = inode.eofIdx,
			lastBlock = inode.blockList.last,
			lastBlockAddr = cfsys.blockMap[lastBlock] |
		fRead[d, add[eofIdx, 1], lastBlockAddr].elems in ErasedData
}

// Every page that is mapped to a file block has the status 'Valid'
pred dataPagesAreValid[cfsys : ConcFsys, d : Device] {
	all inode : FID.(cfsys.inodeMap) |
	all rowAddr : cfsys.blockMap[inode.blockList.elems] |
		// all flags are properly set
		d.pageStatusMap[rowAddr] = Valid
}

// Every page that is not mapped to a file block has the status 'Invalid' or 'Free' 
pred nonDataPagesAreFreeOrInvalid[cfsys : ConcFsys, d: Device] {
	let inodes =  FID.(cfsys.inodeMap) |
	all rowAddr : RowAddr - (cfsys.blockMap[inodes.blockList.elems]) |
		let pageStatus = d.pageStatusMap[rowAddr] |
			pageStatus = Invalid or pageStatus = Free
}

pred freePagesAreErased[d : Device] {
	all rowAddr : RowAddr | 
		let lunAddr = rowAddr.l, blockAddr = rowAddr.b, pageAddr = rowAddr.p,
			page = d.luns[lunAddr].blocks[blockAddr].pages[pageAddr] |
			// all data bits in the page are erased
			(d.pageStatusMap[rowAddr] = Free) => (page.data.elems in ErasedData)
}

pred reclaimReservePagesAreFree[d : Device] {
	all rowAddr : {r : RowAddr | r.b = d.reserveBlock} |
		d.pageStatusMap[rowAddr] = Free
}

// Conditions that must hold true at the initial ConcFsys and Device states
pred concInvariant[cfsys : ConcFsys, d : Device] {
	eofReset[cfsys]
	eofDataErased[cfsys, d]
	dataPagesAreValid[cfsys, d]
 	nonDataPagesAreFreeOrInvalid[cfsys, d]
	freePagesAreErased[d]
	reclaimReservePagesAreFree[d]
}

/********************
 * Test runs
 ********************/
fun test[cfsys : ConcFsys, d : Device, fid : FID,  blockIdx : Int] : seq Data {
	let rowAddr = cfsys.blockMap[cfsys.inodeMap[fid].blockList[blockIdx]] |
		fRead[d, 0, rowAddr]
}

fun testStatus [cfsys : ConcFsys, d : Device, fid : FID, blockIdx : Int] : PageStatus {
	let rowAddr = cfsys.blockMap[cfsys.inodeMap[fid].blockList[blockIdx]] |
		d.pageStatusMap[rowAddr]
}

// Test case #1
run {
	concInvariant[ConcFsys, Device]
	some inodeMap
} for 4 but 1 ConcFsys, 1 Device, 5 int, 8 seq, 6 VBlock, 6 RowAddr

// Test case #2
// read test
run {
	some cfsys : ConcFsys,
			d : Device, fid : FID, offset, size : Int, readData : seq Data |
		readConc [cfsys, d, fid, offset, size, readData] and
		some readData and
		offset = 1
} for 4 but 1 ConcFsys, 1 Device, 5 int, 8 seq, 6 VBlock, 6 RowAddr

// Test case #3
// read test - multiple blocks
run {
	some cfsys : ConcFsys,
			d : Device, fid : FID, readData : seq Data, offset, size : Int |
		readConc [cfsys, d, fid, offset, size, readData] and
		some readData and
		offset = 1 and
		size = 8 and
		(all p : Page | !p.data.hasDups) and
		#cfsys.inodeMap[fid].blockList > 1
} for 4 but 1 ConcFsys, 1 Device, 5 int, 8 seq, 6 VBlock, 6 RowAddr

// Test case #4
// write test - modifying an existing portion of the file
// Success case
run {
	some cfsys, cfsys' : ConcFsys, d, d' : Device, fid : FID, 
			writeData : seq Data, offset, size: Int |
		#(cfsys.inodeMap[fid].blockList) = 1 and
		offset = 3 and
		no (writeData.elems & ErasedData) and
		#writeData > 1 and
		concInvariant[cfsys, d] and
		size > 1 and
		writeConc[cfsys, cfsys', d, d', fid, writeData, offset, size, Succ] 
} for 4 but 2 ConcFsys, 2 Inode, 5 int, 8 seq, 
			1 StateSeqFactory, 4 TranscState, 0 Fail1, 0 Fail2,
			exactly 6 VBlock, exactly 6 RowAddr

// Test case #5
// write test - modifying an existing portion of the file
// Failure case: Phase 1 Crash & Recovery
run {
	some cfsys, cfsys', cfsys'' : ConcFsys, d, d', d'' : Device, fid : FID, 
			writeData : seq Data, offset,size: Int, opResult : OpResult |
		#(cfsys.inodeMap[fid].blockList) = 1 and
		offset = 3 and
		no (writeData.elems & ErasedData) and
		#writeData > 1 and
		concInvariant[cfsys, d] and
		writeConc[cfsys, cfsys', d, d', fid, writeData, offset, size,opResult] and
		opResult = Fail1 and
		recoverFromPowerLoss[cfsys', cfsys'', d', d'', opResult]
} for 3 but 2 ConcFsys, 2 Inode, 5 int, 8 seq, 
			1 StateSeqFactory, 1 Fail1, 0 Fail2,
			6 VBlock, 6 RowAddr

// Test case #6
// write test - modifying an existing portion of the file
// Failure case: Phase 2 Crash & Recovery
run {
	some cfsys, cfsys', cfsys'' : ConcFsys, d, d', d'' : Device, fid : FID, 
			writeData : seq Data, offset,size : Int, opResult : OpResult |
		#(cfsys.inodeMap[fid].blockList) = 1 and
		offset = 3 and
		no (writeData.elems & ErasedData) and
		#writeData > 1 and
		concInvariant[cfsys, d] and
		writeConc[cfsys, cfsys', d, d', fid, writeData, offset, size,opResult] and
		opResult in Fail2 and
		recoverFromPowerLoss[cfsys', cfsys'', d', d'', opResult]
} for 4 but 2 ConcFsys, 5 int, 8 seq, 	
			1 StateSeqFactory, 0 Fail1, 1 Fail2, 
			6 VBlock, 6 RowAddr

// Test case #7
// write test - writing past the current end of the file
run {
	some cfsys, cfsys' : ConcFsys, d, d' : Device, fid : FID, 
			writeData : seq Data, offset,size : Int |
		#(cfsys.inodeMap[fid].blockList) = 1 and
		offset = 5 and
		concInvariant[cfsys, d] and
		writeConc[cfsys, cfsys', d, d', fid, writeData, offset, size, Succ] and
		some writeData and
		writeData.elems not in ErasedData and
		size > 0
} for 4 but 2 ConcFsys, 2 Inode, 5 int, 8 seq, 
			1 StateSeqFactory, 0 Fail1, 0 Fail2,
			6 VBlock, 6 RowAddr

// Test case #8
// write test - writing past the current end of the file
// The gap between the EOF and the offset is greater than the block size
run {
	some cfsys, cfsys' : ConcFsys, d, d' : Device, fid : FID, 
			writeData : seq Data, offset,size : Int |
		#(cfsys.inodeMap[fid].blockList) = 0 and
		offset = 4 and
		concInvariant[cfsys, d] and
		writeConc[cfsys, cfsys', d, d', fid, writeData, offset, size, Succ] and
		some writeData and
		writeData.elems not in ErasedData and
		size > 0
} for 3 but 5 int, 8 seq, 2 ConcFsys, 2 Inode, 
			1 StateSeqFactory, 4 TrscSeq/SeqIdx, 0 Fail1, 0 Fail2, 
			4 Device, 4 LUN, 5 Block, 5 Page, 4 TranscState, 
			6 VBlock, 6 RowAddr

// Test case #9 - similar test case as #8, except the initial file is not empty
// write test - writing past the current end of the file
// The gap between the eof and the offset is greater than the block size
run {
	some cfsys, cfsys' : ConcFsys, d, d' : Device, fid : FID, 
			writeData : seq Data, offset,size : Int |
		#(cfsys.inodeMap[fid].blockList) = 1 and
		offset = 8 and
		concInvariant[cfsys, d] and
		writeConc[cfsys, cfsys', d, d', fid, writeData, offset, size,Succ] and
		some writeData and
		writeData.elems not in ErasedData and
		size > 0
} for 4 but 5 int, 8 seq, 2 ConcFsys, 2 Inode, 
			1 StateSeqFactory,  0 Fail1, 0 Fail2,
			4 Device, 4 LUN, 5 Block, 5 Page, 4 TranscState, 
			6 VBlock, 6 RowAddr

// Test case #10
// Test reclamation followed by write - easy case, doesn't involve backing up valid blocks
run {
	some cfsys, cfsys' : ConcFsys, d, d' : Device, fid : FID, writeData : seq Data, 
              offset,size : Int |
		#(cfsys.inodeMap[fid].blockList) = 1 and
		offset = 0 and
		no searchFreeBlocks[d] and
		test[cfsys, d, fid, 0] != test[cfsys', d', fid, 0] and
		concInvariant[cfsys, d] and
		writeConc[cfsys, cfsys', d, d', fid, writeData, offset, size, Succ]
} for 3 but 5 int, 8 seq, 2 ConcFsys, 2 Inode, 
			2 StateSeqFactory, 5 TrscSeq/SeqIdx, 4 TranscState, 4 Device,
			0 Fail1, 0 Fail2, 6 VBlock, 6 RowAddr

// Test case #11
// Test reclamation followed by write - 
// a more complex case, involves backing up valid blocks
run {
	some cfsys, cfsys' : ConcFsys, d, d' : Device, fid : FID, writeData : seq Data, 
            offset,size : Int |	
		#(cfsys.inodeMap[fid].blockList) = 1 and
		#(searchInvalidBlocks[d]) = 1 and
		offset = 0 and
		no searchFreeBlocks[d] and
		concInvariant[cfsys, d] and
		test[cfsys, d, fid, 0] != test[cfsys', d', fid, 0] and
		writeConc[cfsys, cfsys', d, d', fid, writeData, offset, size, Succ] 
} for 3 but 5 int, 8 seq, 2 ConcFsys, 4 Inode, 
			2 StateSeqFactory, 5 TranscState, 5 Device,
			0 Fail1, 0 Fail2, 6 VBlock, 6 RowAddr

// Reading the file immediately after writing to it results in the same data
// as in the input write buffer
assert WriteSuccOK {
	all cfsys, cfsys' : ConcFsys, d, d' : Device, fid : FID, 
		offset,size : Int, writeBuffer : seq Data |
			(concInvariant[cfsys, d] and
	 		writeConc[cfsys, cfsys', d, d', fid, writeBuffer, offset, size, Succ])
		 =>
			(all readBuffer : seq Data |
				readConc[cfsys', d', fid, 0, add[offset, size], readBuffer] =>
				(readBuffer.subseqFrom[offset] = writeBuffer.subseq[0, sub[size, 1]]))
}

check WriteSuccOK for 
		4 but 5 int, 8 seq, 2 ConcFsys, 1 StateSeqFactory, 0 Fail1, 0 Fail2, 
		 		exactly 6 VBlock, exactly 6 RowAddr

// A write operation preserves the concrete state invariant
assert WriteInvariantOK{
	all cfsys, cfsys' : ConcFsys, d, d' : Device, fid : FID, 
		offset,size : Int, writeBuffer : seq Data |
			(concInvariant[cfsys, d] and
			writeConc[cfsys, cfsys', d, d', fid, writeBuffer, offset, size, Succ]) 
		=>
			(concInvariant[cfsys', d'])
}

check WriteInvariantOK for 
		4 but 5 int, 8 seq, 2 ConcFsys, 1 StateSeqFactory, 0 Fail1, 0 Fail2, 
		 		exactly 6 VBlock, exactly 6 RowAddr

// When a hardware failure occurs in the Phase 1 of the write operation,
// on the reboot, the FFS recovers back to the state at the beginning of the 
// operation. 
assert WritePhaseOneCrashRecoveryOK {
	all cfsys, cfsys', cfsys'' : ConcFsys, d, d', d'' : Device, fid : FID, offset,size: Int, 
		writeBuffer : seq Data |
			(concInvariant[cfsys, d] and
			 writeConc[cfsys, cfsys', d, d', fid, writeBuffer, offset, size, Fail1] and
			 recoverFromPowerLoss[cfsys', cfsys'', d', d'', Fail1]) 
		=>
			(all fid2 : FID, offset2, size : Int, readBuffer : seq Data |
				readConc [cfsys, d, fid2, offset2, size, readBuffer] <=>
				readConc [cfsys'', d'', fid2, offset2, size, readBuffer])
}

check WritePhaseOneCrashRecoveryOK for 
		4 but 5 int, 8 seq, 1 ConcFsys, 1 StateSeqFactory, 0 Fail2, 
				exactly 6 VBlock, exactly 6 RowAddr

// When a hardware failure occurs in the Phase 2 of the write operation,
// on the reboot, the FFS recovers forward to the state at which the operation would
// have completed successfully. 
assert WritePhaseTwoCrashRecoveryOK {
	all cfsys, cfsys', cfsys'' : ConcFsys, d, d', d'' : Device, 
		fid : FID, offset,size : Int, writeBuffer : seq Data, opResult : Fail2 |
			(concInvariant[cfsys, d] and
		 	writeConc[cfsys, cfsys', d, d', fid, writeBuffer, offset,size, opResult] and
		 	recoverFromPowerLoss[cfsys', cfsys'', d', d'', opResult])
		 =>
			(all readBuffer : seq Data |
				readConc[cfsys'', d'', fid, 0, add[offset, #writeBuffer], readBuffer] =>
				(readBuffer.subseqFrom[offset] = writeBuffer))
}

check WritePhaseTwoCrashRecoveryOK for 
		4 but 5 int, 8 seq, 2 ConcFsys, 1 StateSeqFactory, 1 Fail2, 
				exactly 6 VBlock, exactly 6 RowAddr

// Repeating a write operation successfully twice has no effect
assert ConcreteWriteIdempotent {
	all cfsys, cfsys',cfsys'' : ConcFsys, 
		d, d', d'' : Device, 
		fid : FID, offset,size : Int,buffer : seq Data |
			(concInvariant[cfsys, d] and
			 writeConc[cfsys, cfsys', d, d', fid, buffer, offset,size, Succ] and
			 writeConc[cfsys', cfsys'', d', d'', fid, buffer, offset,size, Succ])
	 =>
			(all fid2 : FID, offset2, size2 : Int, buffer2 : seq Data | 
				readConc[cfsys', d', fid2, offset2, size2, buffer2] <=>
				readConc[cfsys'', d'', fid2, offset2, size2, buffer2])
}

check ConcreteWriteIdempotent for 
		4 but 5 int, 8 seq, 3 ConcFsys, 2 StateSeqFactory, 0 Fail2,
				exactly 6 VBlock, exactly 6 RowAddr
