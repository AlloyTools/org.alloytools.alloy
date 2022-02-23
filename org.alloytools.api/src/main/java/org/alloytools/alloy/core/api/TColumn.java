package org.alloytools.alloy.core.api;


public interface TColumn {

    TSignature getSignatures();

    enum TMultiplicity {
                       lone(),
                       one,
                       some,
                       set
    }

    TMultiplicity getMultiplicity();

}
