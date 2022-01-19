package org.alloytools.alloy.lsp.provider;

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.nio.file.Paths;

import org.eclipse.lsp4j.Location;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.Range;
import org.eclipse.lsp4j.jsonrpc.messages.Either;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4whole.SimpleGUI;

public class AlloyLanguageServerUtil {
	public static Pos positionToPos(Position position) {
		return positionToPos(position, null);
	}

	public static Pos positionToPos(Position position, String fileName) {
		return new Pos(fileName, position.getCharacter() + 1, position.getLine() + 1);
	}

	public static Location posToLocation(Pos pos){
		Location res= new Location();
		res.setRange(createRangeFromPos(pos));
		res.setUri(filePathToUri(pos.filename));
		return res;
	}

	public static org.eclipse.lsp4j.Position posToPosition(edu.mit.csail.sdg.alloy4.Pos pos) {
		Position position = new Position();
		position.setLine(pos.y - 1);
		position.setCharacter(pos.x - 1);
		return position;
	}
	public static Range createRange(Position start, Position end) {
		Range res = new Range();
		res.setStart(start);
		res.setEnd(end);
		return res;
	}
	public static Range createRangeFromPos(Pos pos) {
		Range res = new Range();
		res.setStart(posToPosition(pos));

		Position endPosition = new Position();
		endPosition.setLine(pos.y2 - 1);
		endPosition.setCharacter(pos.x2 - 1 + 1 /* end position appears to be exclusive in Range */);

		res.setEnd(endPosition);
		return res;
	}

	public static String filePathToUri(String absolutePath) {
		return Paths.get(absolutePath).toUri().toString();
	}

	public static String fileUriToPath(String fileUri) {
		try {
			File file = new File(new URI(fileUri));
			try {
				return file.getCanonicalPath();
			} catch (IOException ex) {
				return file.getAbsolutePath();
			}
		} catch (Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	public static String filePathResolved(String filename) {
        return filename.replace(Util.jarPrefix(), SimpleGUI.alloyHome(null) + fs);
	}

	/**
	 * Return .getLeft() of the Either object, or throw .getRight()
	 * @return .getLeft() of the Either object if it isLeft()
	 * @throws TErr
	 */
	public static <TRes,TErr extends Exception> TRes getResult(Either<TRes,TErr> val) throws TErr{
		if (val.isRight()) throw val.getRight();
		return val.getLeft();
	}

	/**
	 * The system-specific file separator (forward-slash on UNIX, back-slash on
	 * Windows, etc.)
	 */
	public static final String fs = System.getProperty("file.separator");

}