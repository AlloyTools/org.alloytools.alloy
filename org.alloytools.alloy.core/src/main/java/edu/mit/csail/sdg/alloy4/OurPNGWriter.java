/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4;

import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;

import javax.imageio.ImageIO;

/**
 * Graphical convenience methods for producing PNG files.
 */

public final strictfp class OurPNGWriter {

    /**
     * The constructor is private, since this utility class never needs to be
     * instantiated.
     */
    private OurPNGWriter() {}

    /**
     * Writes the image as a PNG file with the given horizontal and vertical
     * dots-per-inch.
     */
    public static void writePNG(BufferedImage image, String filename, double dpiX, double dpiY) throws IOException {
        try {
            ImageIO.write(image, "PNG", new File(filename)); // some versions of
                                                            // Java
                                                            // sometimes
                                                            // throws an
                                                            // exception
                                                            // during
                                                            // saving...
            setDPI(filename, dpiX, dpiY);
        } catch (Throwable ex) {
            if (ex instanceof IOException)
                throw (IOException) ex;
            if (ex instanceof StackOverflowError)
                throw new IOException("Out of memory trying to save the PNG file to " + filename);
            if (ex instanceof OutOfMemoryError)
                throw new IOException("Out of memory trying to save the PNG file to " + filename);
            throw new IOException("Error writing the PNG file to " + filename + " (" + ex + ")");
        }
    }

    /*
     * PNG consists of a "8 byte header" followed by one or more CHUNK... Each
     * CHUNK: =========== 4 bytes: an integer N expressed with most-significant-byte
     * first 4 bytes: Chunk Type N bytes: Chunk Data 4 bytes: Checksum (this
     * checksum is computed over the Chunk Type and Chunk Data) Each PNG must
     * contain an IDAT chunk (this is the actual pixels of the image) Each PNG may
     * contain an optional pHYs chunk that describes the horizontal and vertical
     * dots-per-meter information. If such a chunk exists, it must come before
     * (though not necessarily immediately before) the IDAT chunk. pHYs CHUNK:
     * =========== 4 bytes: 0 , 0 , 0 , 9 4 bytes: 'p' , 'H' , 'Y' , 's' 4 bytes:
     * horizontal dots per meter (most-significant-byte first) 4 bytes: vertical
     * dots per meter (most-significant-byte first) 1 byte: 1 4 bytes: Checksum
     */

    /**
     * Modifies the given PNG file to have the given horizontal and vertical
     * dots-per-inch.
     */
    private static void setDPI(String filename, double dpiX, double dpiY) throws IOException {
        RandomAccessFile f = null;
        try {
            f = new RandomAccessFile(filename, "rw");
            for (long total = f.length(), pos = 8; pos < total;) { // Jump to
                                                                  // the right
                                                                  // place for
                                                                  // inserting
                                                                  // the pHYs
                                                                  // chunk,
                                                                  // then
                                                                  // insert it
                f.seek(pos);
                int a1 = f.read();
                if (a1 < 0)
                    break;
                int a2 = f.read();
                if (a2 < 0)
                    break;
                int a3 = f.read();
                if (a3 < 0)
                    break;
                int a4 = f.read();
                if (a4 < 0)
                    break;
                int b1 = f.read();
                if (b1 < 0)
                    break;
                int b2 = f.read();
                if (b2 < 0)
                    break;
                int b3 = f.read();
                if (b3 < 0)
                    break;
                int b4 = f.read();
                if (b4 < 0)
                    break;
                int jump = (a1 << 24) | (a2 << 16) | (a3 << 8) | a4;
                if (jump < 0 || (total - pos) - 12 < jump)
                    throw new IOException("PNG chunk size exceeds the rest of the file.");
                if ((b1 == 'I' && b2 == 'D' && b3 == 'A' && b4 == 'T') || (b1 == 'p' && b2 == 'H' && b3 == 'Y' && b4 == 's')) {
                    Util.shift(f, (b1 == 'p' ? (pos + 12 + jump) : pos), pos + 21); // skip
                                                                                   // over
                                                                                   // the
                                                                                   // existing
                                                                                   // pHYs
                                                                                   // chunk
                                                                                   // if
                                                                                   // we
                                                                                   // see
                                                                                   // it
                    f.seek(pos);
                    writeDPI(f, dpiX, dpiY);
                    f.close();
                    f = null;
                    return; // use a "return" rather than "break" so that we
                           // don't enter the line that throws the IOException
                }
                pos = pos + 12 + jump;
            }
            throw new IOException("PNG is missing the IDAT chunk");
        } finally {
            Util.close(f);
        }
    }

    /**
     * Write a "pHYs" chunk into the given file with the given horizontal and
     * vertical dots-per-inch.
     */
    private static void writeDPI(RandomAccessFile file, double dpiX, double dpiY) throws IOException {
        int x = (int) (dpiX / 0.0254), y = (int) (dpiY / 0.0254); // Translate
                                                                 // dots-per-inch
                                                                 // into
                                                                 // dots-per-meter
        writeChunk(file, new int[] {
                                    'p', 'H', 'Y', 's', x >>> 24, x >>> 16, x >>> 8, x, y >>> 24, y >>> 16, y >>> 8, y, 1
        });
    }

    /**
     * Write the given chunk into the given file; Note: data.length must be at least
     * 4.
     */
    private static void writeChunk(RandomAccessFile file, int[] data) throws IOException {
        int crc = (-1), len = data.length - 4;
        file.write((len >>> 24) & 255);
        file.write((len >>> 16) & 255);
        file.write((len >>> 8) & 255);
        file.write(len & 255);
        for (int i = 0; i < data.length; i++) {
            int x = data[i];
            crc = table[(crc ^ x) & 255] ^ (crc >>> 8);
            file.write(x & 255);
        }
        crc = crc ^ (-1);
        file.write((crc >>> 24) & 255);
        file.write((crc >>> 16) & 255);
        file.write((crc >>> 8) & 255);
        file.write(crc & 255);
    }

    /**
     * This precomputed table makes it faster to calculate CRC; this is based on the
     * suggestion in the PNG specification.
     */
    private static final int[] table = new int[] {
                                                  0, 1996959894, -301047508, -1727442502, 124634137, 1886057615, -379345611, -1637575261, 249268274, 2044508324, -522852066, -1747789432, 162941995, 2125561021, -407360249, -1866523247, 498536548, 1789927666, -205950648, -2067906082, 450548861, 1843258603, -187386543, -2083289657, 325883990, 1684777152, -43845254, -1973040660, 335633487, 1661365465, -99664541, -1928851979, 997073096, 1281953886, -715111964, -1570279054, 1006888145, 1258607687, -770865667, -1526024853, 901097722, 1119000684, -608450090, -1396901568, 853044451, 1172266101, -589951537, -1412350631, 651767980, 1373503546, -925412992, -1076862698, 565507253, 1454621731, -809855591, -1195530993, 671266974, 1594198024, -972236366, -1324619484, 795835527, 1483230225, -1050600021, -1234817731, 1994146192, 31158534, -1731059524, -271249366, 1907459465, 112637215, -1614814043, -390540237, 2013776290, 251722036, -1777751922, -519137256, 2137656763, 141376813, -1855689577, -429695999, 1802195444, 476864866, -2056965928, -228458418, 1812370925, 453092731, -2113342271, -183516073, 1706088902, 314042704, -1950435094, -54949764, 1658658271, 366619977, -1932296973, -69972891, 1303535960, 984961486, -1547960204, -725929758, 1256170817, 1037604311, -1529756563, -740887301, 1131014506, 879679996, -1385723834, -631195440, 1141124467, 855842277, -1442165665, -586318647, 1342533948, 654459306, -1106571248, -921952122, 1466479909, 544179635, -1184443383, -832445281, 1591671054, 702138776, -1328506846, -942167884, 1504918807, 783551873, -1212326853, -1061524307, -306674912, -1698712650, 62317068, 1957810842, -355121351, -1647151185, 81470997, 1943803523, -480048366, -1805370492, 225274430, 2053790376, -468791541, -1828061283, 167816743, 2097651377, -267414716, -2029476910, 503444072, 1762050814, -144550051, -2140837941, 426522225, 1852507879, -19653770, -1982649376, 282753626, 1742555852, -105259153, -1900089351, 397917763, 1622183637, -690576408, -1580100738, 953729732, 1340076626, -776247311, -1497606297, 1068828381, 1219638859, -670225446, -1358292148, 906185462, 1090812512, -547295293, -1469587627, 829329135, 1181335161, -882789492, -1134132454, 628085408, 1382605366, -871598187, -1156888829, 570562233, 1426400815, -977650754, -1296233688, 733239954, 1555261956, -1026031705, -1244606671, 752459403, 1541320221, -1687895376, -328994266, 1969922972, 40735498, -1677130071, -351390145, 1913087877, 83908371, -1782625662, -491226604, 2075208622, 213261112, -1831694693, -438977011, 2094854071, 198958881, -2032938284, -237706686, 1759359992, 534414190, -2118248755, -155638181, 1873836001, 414664567, -2012718362, -15766928, 1711684554, 285281116, -1889165569, -127750551, 1634467795, 376229701, -1609899400, -686959890, 1308918612, 956543938, -1486412191, -799009033, 1231636301, 1047427035, -1362007478, -640263460, 1088359270, 936918000, -1447252397, -558129467, 1202900863, 817233897, -1111625188, -893730166, 1404277552, 615818150, -1160759803, -841546093, 1423857449, 601450431, -1285129682, -1000256840, 1567103746, 711928724, -1274298825, -1022587231, 1510334235, 755167117
    };
}
