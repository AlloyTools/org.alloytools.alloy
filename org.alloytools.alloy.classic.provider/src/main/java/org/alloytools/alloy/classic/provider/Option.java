package org.alloytools.alloy.classic.provider;

import aQute.libg.glob.Glob;

class Option implements Comparable<Option> {
	final String	value;
	final Glob		glob;
	final String	key;

	public Option(String glob, String key, String value) {
		if (glob == null)
			this.glob = Glob.ALL;
		else
			this.glob = new Glob(glob);
		this.value = value;
		this.key = key;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((key == null) ? 0 : key.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Option other = (Option) obj;
		if (key == null) {
			if (other.key != null)
				return false;
		} else if (!key.equals(other.key))
			return false;
		return true;
	}

	@Override
	public int compareTo(Option o) {
		return Integer.compare(o.glob.toString()
			.length(),
			this.glob.toString()
				.length());
	}

}