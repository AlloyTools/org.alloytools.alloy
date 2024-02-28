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
package kodkod.doc;


import java.util.Map;

import com.sun.javadoc.Doc;
import com.sun.javadoc.MethodDoc;
import com.sun.javadoc.Tag;
import com.sun.tools.doclets.formats.html.markup.RawHtml;
import com.sun.tools.doclets.internal.toolkit.Content;
import com.sun.tools.doclets.internal.toolkit.taglets.InheritableTaglet;
import com.sun.tools.doclets.internal.toolkit.taglets.Taglet;
import com.sun.tools.doclets.internal.toolkit.taglets.TagletWriter;
import com.sun.tools.doclets.internal.toolkit.util.DocFinder;
import com.sun.tools.doclets.internal.toolkit.util.DocletConstants;

/**
 * Represents a taglet for specification tags:  
 * <code>@specfield</code>, <code>@invariant</code>,
 * <code>@ensures</code>, and <code>@requires</code>.
 * 
 * @specfield name: String
 * 
 * @author Emina Torlak
 */
public final class SpecificationTaglet implements InheritableTaglet {
	private static final int TYPE = 1, FIELD = 2, METHOD = 4, CONSTRUCTOR = 8, PACKAGE = 16, OVERVIEW = 32;
	private final String tagName, tagHeader;
	private int tagLocations;

	/**
	 * Constructs a specification taglet for the given tag name, using the
	 * given header and location specifier.
	 */
	private SpecificationTaglet(String tagName, String tagHeader, int tagLocations) {
		this.tagName = tagName;
		this.tagHeader = tagHeader;
		this.tagLocations = tagLocations;
	}

	/**
	 * Register this Taglet.
	 * @param tagletMap  the map to register this tag to.
	 */
	public static void register(Map<String, Taglet> tagletMap) {
		register(tagletMap, new SpecificationTaglet("specfield", "Specfields:", TYPE));
		register(tagletMap, new SpecificationTaglet("requires", "Requires:", METHOD+CONSTRUCTOR));
		register(tagletMap, new SpecificationTaglet("ensures", "Ensures:", METHOD+CONSTRUCTOR));
		register(tagletMap, new SpecificationTaglet("invariant", "Invariants:", TYPE+METHOD+CONSTRUCTOR+FIELD));
		}

	/**
	 * Adds the given taglet to the map.
	 */
	private static void register(Map<String, Taglet> tagletMap, Taglet taglet) {
		final Taglet current = tagletMap.get(taglet.getName());
		if (current != null)
			tagletMap.remove(taglet.getName());
		tagletMap.put(taglet.getName(), taglet);

	}

	/**
	 * {@inheritDoc}
	 * @see com.sun.tools.doclets.internal.toolkit.taglets.Taglet#getName()
	 */
	@Override
	public String getName() { return tagName; }

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void inherit(DocFinder.Input input, DocFinder.Output output) {
		if (input.element != null && input.element.isMethod()) {
			final Tag[] tags = input.element.tags(tagName);
			if (tags.length > 0) {
				output.holder = input.element;
				output.holderTag = tags[0];
				output.inlineTags = input.isFirstSentence ?
						tags[0].firstSentenceTags() : tags[0].inlineTags();
			} 
		} 
	}

	/**
	 * Appends the formatted definition header to the given buffer.
	 * @return out
	 */
	private StringBuilder writeHeader(StringBuilder out) {
		return out.append(DocletConstants.NL)
				.append("<DT><B>").append(tagHeader).append("</B></DT>");
	}
	
	/**
	 * Appends the formatted definition tag to the given buffer.
	 * @return out
	 */
	private StringBuilder writeTag(StringBuilder out, Tag tag, TagletWriter writer) {
		return out.append(DocletConstants.NL)
				.append("<DD><CODE>")
				.append(writer.commentTagsToOutput(tag, null, tag.inlineTags(), false))
				.append("</CODE></DD>");
	}
	/**
	 * {@inheritDoc}
	 */
	@Override
	public Content getTagletOutput(Tag tag, TagletWriter writer) throws IllegalArgumentException {
		final StringBuilder out = writeTag(writeHeader(new StringBuilder()), tag, writer);
		return new RawHtml(out.toString());
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public Content getTagletOutput(Doc doc, TagletWriter writer) throws IllegalArgumentException {
		Tag[] tags = doc.tags(getName());
		if (tags.length==0 && doc instanceof MethodDoc) { // inherit if necessary and possible
			final DocFinder.Output inheritedDoc = DocFinder.search(new DocFinder.Input((MethodDoc) doc, this));
			tags = inheritedDoc.holderTag == null ? tags : new Tag[] {inheritedDoc.holderTag};
		}
		if (tags.length==0)
			return null;
		final StringBuilder out = writeHeader(new StringBuilder());
		for(Tag tag : tags) { 
			writeTag(out, tag, writer);
		}
		return new RawHtml(out.toString());
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean inConstructor() { return (tagLocations & CONSTRUCTOR) != 0; }

	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean inField() { return (tagLocations & FIELD) != 0; }

	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean inMethod() { return (tagLocations & METHOD) != 0; } 

	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean inOverview() { return (tagLocations & OVERVIEW) != 0; }

	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean inPackage() { return (tagLocations & PACKAGE) != 0; }

	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean inType() { return (tagLocations & TYPE) != 0; }

	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean isInlineTag() { return false; }


}
