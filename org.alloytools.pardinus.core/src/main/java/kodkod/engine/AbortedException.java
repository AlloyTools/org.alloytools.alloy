/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.engine;

/**
 * Indicates that a solving or evaluation task has been aborted.
 * @author Emina Torlak
 */
public final class AbortedException extends RuntimeException {

	private static final long serialVersionUID = 201522560152091247L;

	/**
	 * Constructs an aborted exception with no message.
	 */
	AbortedException() {}

	/**
	 * Constructs an aborted exception with the given message.
	 */
	AbortedException(String message) {
		super(message);
	}

	/**
	 * Constructs an aborted exception with the given cause.
	 */
	AbortedException(Throwable cause) {
		super(cause); 
	}

	/**
	 * Constructs an aborted exception with the given message and cause.
	 */
	AbortedException(String message, Throwable cause) {
		super(message, cause);
	}

}
