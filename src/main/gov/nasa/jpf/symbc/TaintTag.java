package gov.nasa.jpf.symbc;

import java.io.Serializable;

/**
 * Typed taint metadata carried as a JPF attribute.
 *
 * JPF stores attributes on operands, locals, fields, array elements, frames,
 * and heap objects. Keeping taint as its own type lets listeners distinguish it
 * from symbolic expression attributes that SPF already attaches.
 */
public final class TaintTag implements Serializable {
    private static final long serialVersionUID = 1L;

    private final String source;
    private final String origin;

    public TaintTag(String source, String origin) {
        this.source = source;
        this.origin = origin;
    }

    public String getSource() {
        return source;
    }

    public String getOrigin() {
        return origin;
    }

    @Override
    public String toString() {
        return "TaintTag{source='" + source + "', origin='" + origin + "'}";
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) return true;
        if (!(other instanceof TaintTag)) return false;
        TaintTag that = (TaintTag) other;
        return source.equals(that.source) && origin.equals(that.origin);
    }

    @Override
    public int hashCode() {
        int result = source.hashCode();
        result = 31 * result + origin.hashCode();
        return result;
    }
}
