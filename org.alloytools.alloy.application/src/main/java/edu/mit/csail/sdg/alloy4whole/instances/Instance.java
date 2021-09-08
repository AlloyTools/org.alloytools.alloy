package edu.mit.csail.sdg.alloy4whole.instances;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;

import com.fasterxml.jackson.annotation.JsonProperty;

import edu.uiowa.alloy2smt.utils.AlloyUtils;

@XmlRootElement(
                name = "instance" )
public class Instance {

    @XmlElement(
                name = "sig" )
    @JsonProperty("signatures" )
    public List<Signature> signatures;

    @XmlElement(
                name = "field" )
    @JsonProperty("fields" )
    public List<Field>     fields;

    @XmlAttribute(
                  name = "bitwidth" )
    @JsonProperty("bitWidth" )
    public int             bitWidth = 4;

    @XmlAttribute(
                  name = "maxseq" )
    @JsonProperty("maxSeq" )
    public int             maxSeq   = 4;

    @XmlAttribute(
                  name = "mintrace" )
    @JsonProperty("minTrace" )
    public int             minTrace = -1;

    @XmlAttribute(
                  name = "maxtrace" )
    @JsonProperty("maxTrace" )
    public int             maxTrace = -1;

    @XmlAttribute(
                  name = "command" )
    @JsonProperty("command" )
    public String          command;

    @XmlAttribute(
                  name = "filename" )
    @JsonProperty("fileName" )
    public String          fileName;

    @XmlAttribute(
                  name = "tracelength" )
    @JsonProperty("traceLength" )
    public int             traceLength = 1;

    @XmlAttribute(
                  name = "backloop" )
    @JsonProperty("backLoop" )
    public int             backLoop    = 0;

    public String generateAlloyCode() {
        Set<String> allAtoms = new HashSet<>();
        StringBuilder code = new StringBuilder();
        for (Signature signature : signatures) {
            code.append(generateSignatureCode(signature, allAtoms));
        }
        if (allAtoms.size() > 0) {
            List<String> atoms = new ArrayList<>(allAtoms);
            code.append("one sig ");
            code.append(atoms.get(0));
            for (int i = 1; i < atoms.size(); i++) {
                code.append(", " + atoms.get(i));
            }
            code.append(" in univ {}\n");
        }

        if (fields != null) {
            for (Field field : fields) {
                code.append(generateFieldCode(field));
            }
        }

        return code.toString();
    }

    private String generateSignatureCode(Signature signature, Set<String> allAtoms) {
        if (signature.builtIn != null && signature.builtIn.equals("yes")) {
            return "";
        } else {
            if (signature.atoms != null && signature.atoms.size() > 0) {
                // the signature is equal to the union of all atoms
                StringBuilder code = new StringBuilder();
                String atom = AlloyUtils.sanitizeAtom(signature.atoms.get(0).label);
                code.append("fact { " + signature.label.replace("this/", "") + " = " + atom);
                allAtoms.add(atom);
                for (int i = 1; i < signature.atoms.size(); i++) {
                    atom = AlloyUtils.sanitizeAtom(signature.atoms.get(i).label);
                    allAtoms.add(atom);
                    code.append(" + " + atom);
                }
                code.append(" }\n");
                if (signature.isPrivate == null || !signature.isPrivate.equals("yes")) {
                    return code.toString();
                } else {
                    return "";
                }
            }
            // no atoms means cardinality is zero
            return "fact { #" + signature.label.replace("this/", "") + " = 0 }\n";
        }
    }

    private String generateFieldCode(Field field) {
        if (field.tuples != null && field.tuples.size() > 0) {
            StringBuilder code = new StringBuilder();
            // the field is equal to the union of all tuples

            code.append("fact { " + field.label + " = " + generateTupleCode(field.tuples.get(0)));
            for (int i = 1; i < field.tuples.size(); i++) {
                code.append(" + " + generateTupleCode(field.tuples.get(i)));
            }
            code.append(" }\n");
            if (field.isPrivate == null || !field.isPrivate.equals("yes")) {
                return code.toString();
            } else {
                return "";
            }
        } else {
            // no atoms means cardinality is zero
            return "fact { #" + field.label + " = 0 } \n";
        }
    }

    private String generateTupleCode(Tuple tuple) {
        StringBuilder code = new StringBuilder();
        code.append(AlloyUtils.sanitizeAtom(tuple.atoms.get(0).label));
        for (int i = 1; i < tuple.atoms.size(); i++) {
            code.append(" -> " + AlloyUtils.sanitizeAtom(tuple.atoms.get(i).label));
        }
        return code.toString();
    }
}
