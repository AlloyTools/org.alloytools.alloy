package org.alloytools.alloy.dto;

/**
 * The Alloy cardinalities
 */
public enum Cardinality {
                         /**
                          * no tuples
                          */
                         none,
                         /**
                          * 0 or 1 tuple
                          */
                         lone,
                         /**
                          * one tuple (the default)
                          */

                         one,
                         /**
                          * 1 or more tuples
                          */
                         some,
                         /**
                          * any number of tuples
                          */
                         set;
}
