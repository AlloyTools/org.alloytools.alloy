package edu.mit.csail.sdg.alloy4whole.instances;

import com.fasterxml.jackson.annotation.JsonProperty;

import edu.mit.csail.sdg.ast.Sig;
import edu.uiowa.alloy2smt.utils.AlloyUtils;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import java.util.List;

@XmlRootElement(name = "instance")
public class Instance
{
    @XmlElement(name = "sig")
    @JsonProperty("signatures")
    public List<Signature> signatures;

    @XmlElement(name = "field")
    @JsonProperty("fields")
    public List<Field> fields;

    @XmlAttribute(name = "bitwidth")
    @JsonProperty("bitWidth")
    public int bitWidth = 4;

    @XmlAttribute(name = "maxseq")
    @JsonProperty("maxSeq")
    public int maxSeq = 4;

    @XmlAttribute(name = "command")
    @JsonProperty("command")
    public String command;

    @XmlAttribute(name = "filename")
    @JsonProperty("fileName")
    public String fileName;

    public String generateAlloyCode()
    {
        StringBuilder code = new StringBuilder();
        for (Signature signature: signatures)
        {
            code.append(generateSignatureCode(signature));
        }

        for (Field field: fields)
        {
            code.append(generateFieldCode(field));
        }

        return code.toString();
    }

    private String generateSignatureCode(Signature signature)
    {
        if(signature.atoms != null && signature.atoms.size() > 0)
        {
            StringBuilder code = new StringBuilder();
            if(signature.builtIn.equals("yes"))
            {
                if(signature.label.equals(Sig.UNIV.label))
                {
                    // generate singleton signatures for each atom
                    code.append("one sig ");
                    code.append(AlloyUtils.sanitizeAtom(signature.atoms.get(0).label));
                    for (int i = 1; i < signature.atoms.size(); i++)
                    {
                        code.append(", " + AlloyUtils.sanitizeAtom(signature.atoms.get(i).label));
                    }
                    code.append(" in " + signature.label + " {}\n");

                    return code.toString();
                }
            }
            else
            {
                // the signature is equal to the union of all atoms
                code.append("fact { " + signature.label.replace("this/", "") + " = " +
                        AlloyUtils.sanitizeAtom(signature.atoms.get(0).label));
                for (int i = 1; i < signature.atoms.size(); i++)
                {
                    code.append(" + " + AlloyUtils.sanitizeAtom(signature.atoms.get(i).label));
                }
                code.append(" }\n");
            }
            return code.toString();
        }
        return "";
    }

    private String generateFieldCode(Field field)
    {
        if(field.tuples != null && field.tuples.size() > 0)
        {
            StringBuilder code = new StringBuilder();
            // the field is equal to the union of all tuples

            code.append("fact { " + field.label + " = " + generateTupleCode(field.tuples.get(0)));
            for (int i = 1; i < field.tuples.size(); i++)
            {
                code.append(" + " + generateTupleCode(field.tuples.get(i)));
            }
            code.append(" }\n");
            return code.toString();
        }
        return "";
    }

    private String generateTupleCode(Tuple tuple)
    {
        StringBuilder code = new StringBuilder();
        code.append(AlloyUtils.sanitizeAtom(tuple.atoms.get(0).label));
        for(int i = 1; i < tuple.atoms.size(); i++)
        {
            code.append(" -> " + AlloyUtils.sanitizeAtom(tuple.atoms.get(i).label));
        }
        return code.toString();
    }
}
