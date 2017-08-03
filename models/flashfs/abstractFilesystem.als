module VSR/abstractFilesystem [Data, FID]

// Alloy model of the POSIX filesystem
// Author: Eunsuk Kang, May. 2008

// Based on the UNIX file system specification from:
// C. Morgan and B. Sufrin. Specification of the UNIX Filing System.  In 
// Transactions on Software Engineering, volume SE-10, pages 128-142, 
// IEEE, 1984

// A file is a sequence of Data elements
sig File {
	contents : seq Data
}

// Blank data element
one sig ZeroData in Data {}

// A filesystem contains a map from a file ID to a single file
sig AbsFsys {
	//fileMap : FID lone -> one File,
	fileMap : FID -> lone File
}

/********************************
 * Promotion *
 ********************************/

// promotion for the write operation
pred promote [fsys, fsys' : AbsFsys, file, file' : File,  fid : FID] {
	file = fsys.fileMap[fid]
	fsys'.fileMap = fsys.fileMap ++ (fid -> file')
}

/********************************
 * Util functions *
 ********************************/
// Return the subsequence starting at from to the end of the sequence
fun subseqFrom [s : seq Data, from : Int] : seq Data {
	s.subseq[from, #s - 1]
}

// Return a sequence of zero data of the specified length
fun zeros[length : Int] : seq ZeroData {
	{i : Int, fd : ZeroData | i >= 0 and i < length}
}

// Shift the index in the sequence "s" by "offset"
fun shift [s : seq Data, offset : Int] : Int -> Data {
	{index : Int, data : Data |
		some i  : Int |
			i -> data in s and
			i = sub[index, offset]
	}
}

/********************************
 * Abstract operations *
 ********************************/
// input preconditions for the read operation
pred readPreconds[offset, size : Int] {
	offset >= 0 
	size >= 0
}

/*
	Read operation
	input:
		fsys: a Filesystem instance
		fid: ID of the file to read from
		offset: the location within the file to start reading
		size: the number of data elements to read
	output: 
		a sequence of data of length "size" starting at "offset" within the file
*/
fun readAbs [fsys : AbsFsys, fid : FID, offset, size : Int] : seq Data {
	let file = fsys.fileMap[fid] |			
		readPreconds[offset, size] => 
			(file.contents).subseq[offset, sub[add[offset, size], 1]]
		else
			(file.contents).subseq[0, -1]
}

// input preconditions for the read operation
pred writePreconds[buffer : seq Data, offset, size : Int] {
	offset >= 0 
	size >= 0
	size <= #buffer
}

/*
	Write operation
	input:
		fsys, fsys': pre- and post- filesystem states
		fid: ID of the file to read from
		offset: the startng location within the file
		size: the number of data elements to write from buffer
*/
pred writeAbs [fsys, fsys' : AbsFsys, fid : FID, buffer : seq Data, offset, size : Int] {
	writePreconds[buffer, offset, size]
	let buffer' = buffer.subseq[0, sub[size, 1]], 
		 file = fsys.fileMap[fid], file' = fsys'.fileMap[fid] {
			(#buffer' = 0) =>file = file'
			(#buffer' != 0) => 
				file'.contents = (zeros[offset] ++ file.contents) ++ (shift[buffer', offset])
			promote[fsys, fsys', file, file', fid]
	}	
}

/********************************
 * Facts *
 ********************************/
fact CanonicalizeFileContents {
	no disj f1, f2 : File | 
		f1.contents = f2.contents
}	

/********************************
 * Test functions/runs *
 ********************************/
// test a read operation
run {
	some fsys : AbsFsys, fid : FID, offset, size : Int, buffer : seq Data |
		buffer = readAbs[fsys, fid, offset, size] and
		#buffer > 0
} for 4 but exactly 1 AbsFsys

// test a write operation
run {
	some fsys, fsys' : AbsFsys, fid : FID, buffer : seq Data, offset, size  : Int |
		writeAbs[fsys, fsys', fid, buffer, offset, size] and
		offset > 0 and
		#Data > 2 and
		#buffer > 2 and
		(let f = fsys.fileMap[FID], f' = fsys'.fileMap[FID] |
			f'.contents != f.contents
		)
} for 4 but exactly 2 AbsFsys

// Repeating a write operation has no effect
assert WriteIdempotent {
	all fsys, fsys', fsys'' : AbsFsys, fid : FID, offset, size : Int, buffer : seq Data |
		(writeAbs[fsys, fsys', fid, buffer, offset, size] and
		 writeAbs[fsys', fsys'', fid, buffer, offset, size]) =>
		(all fid2 : FID, offset2, size2 : Int | 
			readAbs[fsys', fid2, offset2, size2] =
			readAbs[fsys'', fid2, offset2, size2])
}

// Writing to a particular file does not affect other files in the filesystem
assert WriteLocal {
	all fsys, fsys' : AbsFsys, fid : FID, offset, size : Int, buffer : seq Data |
		writeAbs[fsys, fsys', fid, buffer, offset, size] =>
		(all fid2 : (FID - fid), offset2, size2 : Int |
		 readAbs[fsys, fid2,offset2, size2] =
		 readAbs[fsys', fid2,offset2, size2])
}

check WriteIdempotent for 5 but 5 int, 8 seq
check WriteLocal for 12 but 6 int, 18 seq
