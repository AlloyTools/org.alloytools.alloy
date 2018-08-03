package edu.mit.csail.sdg.alloy4whole;

import java.io.File;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.file.Paths;

import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.Range;

import edu.mit.csail.sdg.alloy4.Pos;

public class AlloyLanguageServerUtil {
	public static Pos positionToPos(Position position) {
		return positionToPos(position, null);
	}

	public static Pos positionToPos(Position position, String fileName) {
		return new Pos(fileName, position.getCharacter() + 1, position.getLine() + 1);
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
		endPosition.setCharacter(pos.x2 - 1);
		
		res.setEnd(endPosition);
		return res;
	}

	public static String filePathToUri(String absolutePath) {
		return Paths.get(absolutePath).toUri().toString();
	}
	
	public static String fileUriToPath(String fileUri) {
		try {
			return new File(new URI(fileUri)).getAbsolutePath();
		} catch (URISyntaxException e) {
			throw new RuntimeException(e);
		}
	}
}
