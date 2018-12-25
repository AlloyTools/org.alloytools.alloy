package edu.uiowa.alloy2smt.mapping;

import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.translators.Translation;
import edu.uiowa.alloy2smt.translators.TranslatorUtils;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

class MapperTests
{
    @Test
    void signature1()
    {
        String alloy = "sig A {} \n fact f {#A = 3}";
        Translation translation = Utils.translate(alloy);
        Assertions.assertNotNull(translation.mapper);

        MappingSignature signature = translation.mapper.signatures
                .stream().filter(s -> s.label.equals("this/A"))
                .findFirst().get();


        Assertions.assertFalse(signature.builtIn);
        Assertions.assertFalse(signature.isAbstract);
        Assertions.assertFalse(signature.id < TranslatorUtils.UNIV_SIGNATURE_ID);
        Assertions.assertEquals(TranslatorUtils.UNIV_SIGNATURE_ID, signature.parentId);
        Assertions.assertEquals("this_A", signature.functionName);
    }
}