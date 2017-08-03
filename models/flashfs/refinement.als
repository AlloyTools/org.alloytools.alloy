module VSR/refinement

open VSR/abstractFilesystem [Data, FID] as PA
open VSR/concreteFilesystem [Data, FID] as PC

// Abstraction function and refinement between the flash (concrete) filesystem
// and the POSIX (abstract) filesystem.
// Author: Eunsuk Kang, May. 2008

// File descriptor
sig FID {}

// Data element
sig Data {}

// Erased data type in the abstract filesystem is equal to that in the concrete world
fact ErasedDataEquivalency {
	PA/ZeroData = PC/FD/ErasedData	
}

// Given a virtual block ID, find the corresponding page on the flash device
fun findPage[blockID : VBlock, concFsys : ConcFsys, d : Device] : Page {
	let rowAddr = concFsys.blockMap[blockID],
		lunAddr = rowAddr.l, blockAddr = rowAddr.b, pageAddr = rowAddr.p |
	d.luns[lunAddr].blocks[blockAddr].pages[pageAddr]
}

/* 
	Abstraction relation
	Maps a concrete state (concFsys, d) to an abstract state (absFsys) by 
	reading off data from each virtual block in the concrete file and
	combining them into a single sequence, which represents the contents of
	an abstract file
*/
pred alpha [concFsys : ConcFsys, absFsys : AbsFsys, d : Device] {
	let pageSize = PC/FD/PAGE_SIZE |
	all fid : FID {
		let inode = concFsys.inodeMap[fid], file = absFsys.fileMap[fid],
			blocks = inode.blockList, endOfDataIdx = inode.eofIdx |
		// the last block in the concrete file may not be full
		// #file.contents = (#blocks - 1)*pageSize + endOfDataIdx + 1
		#file.contents = add[add[mul[sub[#blocks, 1], pageSize], endOfDataIdx], 1] and
		(all indx : blocks.inds | 
		let vblockID = blocks[indx],
			dataFrag = findPage[vblockID, concFsys, d].data,
			from = mul[pageSize, indx], 
			to = sub[add[from,pageSize], 1] |
			((indx = blocks.lastIdx) =>
				file.contents.subseq[from,add[from, endOfDataIdx]] = 
					dataFrag.subseq[0, inode.eofIdx]
			else 
		 		file.contents.subseq[from,to] = dataFrag))
	}
}

pred testAbstract[]{
	some concFsys : ConcFsys, absFsys : AbsFsys, d : Device |
		concInvariant[concFsys, d] and
		alpha[concFsys, absFsys, d] and
		// the rest are constraints to get interesting system configurations
		some concFsys.inodeMap and
		some absFsys.fileMap and
		some inode : univ.(concFsys.inodeMap) | some inode.blockList
		#File.contents > 4 and
		#Page > 1
}

// test for the abstraction relation
//run testAbstract for 5 but exactly 1 File, 1 Device, 1 ConcFsys, 1 AbsFsys, 6 VBlock, 6 RowAddr
pred readTest[] {
	some concFsys : ConcFsys, absFsys : AbsFsys, d : Device, fid : FID,
		buffer : seq Data, offset, size : Int |
		concInvariant[concFsys, d] and
		readConc[concFsys, d, fid, offset, size, buffer] and 
		alpha[concFsys, absFsys, d] and
		buffer = readAbs[absFsys, fid, offset, size]
}

// read test
run readTest for 3 but 1 AbsFsys, 1 ConcFsys, 1 Device, 0 StateSeqFactory, 0 Fail1, 0 Fail2, 
				5 int, 8 seq, exactly 6 VBlock, exactly 6 RowAddr
run readTest for 4 but 1 AbsFsys, 1 ConcFsys, 1 Device, 0 StateSeqFactory, 0 Fail1, 0 Fail2, 
				5 int, 8 seq, exactly 6 VBlock, exactly 6 RowAddr
run readTest for 5 but 1 AbsFsys, 1 ConcFsys, 1 Device, 0 StateSeqFactory, 0 Fail1, 0 Fail2, 
				5 int, 8 seq, exactly 6 VBlock, exactly 6 RowAddr
run readTest for 6 but 1 AbsFsys, 1 ConcFsys, 1 Device, 0 StateSeqFactory, 0 Fail1, 0 Fail2, 
				5 int, 8 seq, exactly 6 VBlock, exactly 6 RowAddr
run readTest for 7 but 1 AbsFsys, 1 ConcFsys, 1 Device, 0 StateSeqFactory, 0 Fail1, 0 Fail2, 
				5 int, 8 seq, exactly 6 VBlock, exactly 6 RowAddr

// checking the refinement for the read operation
assert readRefinement {
	all concFsys : ConcFsys, absFsys : AbsFsys, d : Device, fid : FID,
		buffer : seq Data, offset, size : Int |
			(concInvariant[concFsys, d] and
			readConc[concFsys, d, fid, offset, size, buffer] and 
			alpha[concFsys, absFsys, d]) 
		=>
			(buffer = readAbs[absFsys, fid, offset, size])
}

check readRefinement for 
		3 but 1 AbsFsys, 1 ConcFsys, 1 Device, 0 StateSeqFactory, 0 Fail1, 0 Fail2, 
				5 int, 8 seq, exactly 6 VBlock, exactly 6 RowAddr
check readRefinement for 
		4 but 1 AbsFsys, 1 ConcFsys, 1 Device, 0 StateSeqFactory, 0 Fail1, 0 Fail2, 
				5 int, 8 seq, exactly 6 VBlock, exactly 6 RowAddr
check readRefinement for 
		5 but 1 AbsFsys, 1 ConcFsys, 1 Device, 0 StateSeqFactory, 0 Fail1, 0 Fail2, 
				5 int, 8 seq, exactly 6 VBlock, exactly 6 RowAddr
check readRefinement for 
		6 but 1 AbsFsys, 1 ConcFsys, 1 Device, 0 StateSeqFactory, 0 Fail1, 0 Fail2, 
				5 int, 8 seq, exactly 6 VBlock, exactly 6 RowAddr

pred writeTest[] {
	some disj concFsys, concFsys' : ConcFsys, disj absFsys, absFsys' : AbsFsys, 
		disj d, d' : Device, fid : FID, buffer : seq Data, offset,size : Int |
			concInvariant[concFsys, d] and
			writeConc[concFsys, concFsys', d, d', fid, buffer, offset,size, Succ] and
			alpha[concFsys, absFsys, d] and
	 		alpha[concFsys', absFsys', d'] and
			writeAbs[absFsys, absFsys', fid, buffer, offset, size]
}

run writeTest  for 3 but exactly 2 AbsFsys, exactly 2 ConcFsys, 1 StateSeqFactory, 0 Fail1, 0 Fail2, 
				5 int, 8 seq, exactly 6 VBlock, exactly 6 RowAddr
run writeTest  for 4 but exactly 2 AbsFsys, exactly 2 ConcFsys, 1 StateSeqFactory, 0 Fail1, 0 Fail2, 
				5 int, 8 seq, exactly 6 VBlock, exactly 6 RowAddr
run writeTest  for 5 but exactly 2 AbsFsys, exactly 2 ConcFsys, 1 StateSeqFactory, 0 Fail1, 0 Fail2, 
				5 int, 8 seq, exactly 6 VBlock, exactly 6 RowAddr
run writeTest  for 6 but exactly 2 AbsFsys, exactly 2 ConcFsys, 1 StateSeqFactory, 0 Fail1, 0 Fail2, 
				5 int, 8 seq, exactly 6 VBlock, exactly 6 RowAddr
run writeTest  for 7 but exactly 2 AbsFsys, exactly 2 ConcFsys, 1 StateSeqFactory, 0 Fail1, 0 Fail2, 
				5 int, 8 seq, exactly 6 VBlock, exactly 6 RowAddr

// checking the refinement for the write operation
assert writeRefinement {
	all concFsys, concFsys' : ConcFsys, absFsys, absFsys' : AbsFsys, 
		d, d' : Device, fid : FID, buffer : seq Data, offset,size : Int |
			((concInvariant[concFsys, d] and
			writeConc[concFsys, concFsys', d, d', fid, buffer, offset, size, Succ] and
		 	alpha[concFsys, absFsys, d] and
		 	alpha[concFsys', absFsys', d']) 
		=>
			(writeAbs[absFsys, absFsys', fid, buffer, offset,  size]))
}

check writeRefinement for 
		4 but exactly 2 AbsFsys, exactly 2 ConcFsys, 1 StateSeqFactory, 0 Fail1, 0 Fail2, 
				5 int, 8 seq, 5 Block, 5 Page, exactly 6 VBlock, exactly 6 RowAddr
