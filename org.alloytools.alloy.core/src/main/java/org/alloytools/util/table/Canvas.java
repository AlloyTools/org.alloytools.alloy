package org.alloytools.util.table;

import java.util.Arrays;

public class Canvas {
	// n
	// |
	// w - + - e
	// |
	// s

	final static int	north	= 0b0001;
	final static int	east	= 0b0010;
	final static int	south	= 0b0100;
	final static int	west	= 0b1000;
	final static int	none	= 0;

	final char[]		buffer;
	final int			width;

	public Canvas(int width, int height) {
		this.buffer = new char[width * height];
		this.width = width;
		clear();
	}

	public Canvas clear() {
		return clear(' ');
	}

	public Canvas clear(char c) {
		Arrays.fill(buffer, c);
		return this;
	}

	public Canvas box(int x, int y, int w, int h) {
		bounds(x, y);
		w--;
		h--;
		bounds(x + w, y + h);
		line(x + 1, y, x + w - 1, y, east + west);
		line(x + w, y + 1, x + w, y + h - 1, north + south);
		line(x + 1, y + h, x + w - 1, y + h, east + west);
		line(x, y + 1, x, y + h - 1, north + south);
		merge(x, y, east + south);
		merge(x + w, y, west + south);
		merge(x, y + h, east + north);
		merge(x + w, y + h, north + west);
		return this;
	}

	public Canvas line(int x1, int y1, int x2, int y2, int what) {
		return line(x1, y1, x2, y2, (char) what);
	}

	public Canvas line(int x1, int y1, int x2, int y2, char what) {
		int d = 0;

		int dx = Math.abs(x2 - x1);
		int dy = Math.abs(y2 - y1);

		int dx2 = 2 * dx; // slope scaling factors to
		int dy2 = 2 * dy; // avoid floating point

		int ix = x1 < x2 ? 1 : -1; // increment direction
		int iy = y1 < y2 ? 1 : -1;

		int x = x1;
		int y = y1;

		if (dx >= dy) {
			while (true) {
				merge(x, y, what);
				if (x == x2)
					break;
				x += ix;
				d += dy2;
				if (d > dx) {
					y += iy;
					d -= dx2;
				}
			}
		} else {
			while (true) {
				merge(x, y, what);
				if (y == y2)
					break;
				y += iy;
				d += dx2;
				if (d > dy) {
					x += ix;
					d -= dy2;
				}
			}
		}
		return this;
	}

	public Canvas merge(int x, int y, int what) {
		return merge(x, y, (char) what);
	}

	public Canvas merge(int x, int y, char what) {
		char c = get(x, y);
		if (what >= 16 || c >= 16) {
			set(x, y, what);
		} else {
			set(x, y, (char) (what | c));
		}
		return this;
	}

	public char set(int x, int y, char what) {
		bounds(x, y);
		int index = y * width + x;
		char old = buffer[index];
		buffer[index] = what;
		return old;
	}

	public char get(int x, int y) {
		bounds(x, y);
		return buffer[y * width + x];
	}

	private void bounds(int x, int y) {
		if (x < 0)
			throw new IllegalArgumentException(" x < 0 " + x);
		if (y < 0)
			throw new IllegalArgumentException(" y < 0 " + y);
		if (x >= width)
			throw new IllegalArgumentException("x " + x + " is too high, max " + width);
		if (y >= height())
			throw new IllegalArgumentException("y " + y + " is too high, max " + height());
	}

	public int width() {
		return width;
	}

	public int height() {
		return buffer.length / width;
	}

	public String toString() {
		StringBuilder sb = new StringBuilder();
		toString(sb);
		return sb.toString();
	}

	public void toString(StringBuilder sb) {
		for (int y = 0; y < height(); y++) {
			for (int x = 0; x < width; x++) {
				char c = get(x, y);
				if (c < 16) {
					c = boxchar(c);
				}
				sb.append(c);
			}
			sb.append("\n");
		}
	}

	private char boxchar(char c) {
		switch ((int) c) {
		case north + south:
			return '│';
		case east + west:
			return '─';

		case east + south:
			return '┌';
		case south + west:
			return '┐';
		case north + west:
			return '┘';
		case north + east:
			return '└';

		case east + south + west:
			return '┬';
		case east + north + west:
			return '┴';
		case north + south + west:
			return '┤';
		case east + north + south:
			return '├';
		default:
		case east + north + south + west:
			return '┼';
		}
	}

	public Canvas box() {
		box(0, 0, width(), height());
		return this;
	}

	public Canvas merge(Canvas secondary, int dx, int dy) {
		for (int y = 0; y < secondary.height() && dy + y < height(); y++) {
			for (int x = 0; x < secondary.width() && dx + x < width(); x++) {
				if (dy + y >= 0 && dx + x >= 0) {
					char c = secondary.get(x, y);
					merge(dx + x, dy + y, c);
				}
			}
		}
		return this;
	}

	public void set(int x, int y, String message) {
		for ( int i =0; i<message.length(); i++) {
			if ( x+i < width() && y < height()) {
				set(x+i,y,message.charAt(i));
			}
		}
		
	}
}
