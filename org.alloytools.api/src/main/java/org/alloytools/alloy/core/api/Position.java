package org.alloytools.alloy.core.api;

public interface Position extends Comparable<Position> {

    String getPath();

    int x0();

    int y0();

    int x1();

    int y1();

    int width();

    int height();

    Position merge(Position other);

    boolean contains(Position other);


    default boolean isUnknown() {
        return false;
    }

    static Position unknown() {
        return new Position() {

            @Override
            public int compareTo(Position o) {
                return -1;
            }

            @Override
            public int x0() {
                return 1;
            }

            @Override
            public int y0() {
                return 1;
            }

            @Override
            public int x1() {
                return 1;
            }

            @Override
            public int y1() {
                return 1;
            }

            @Override
            public int width() {
                return 0;
            }

            @Override
            public int height() {
                return 0;
            }

            @Override
            public Position merge(Position other) {
                return other;
            }

            @Override
            public boolean contains(Position other) {
                return false;
            }

            @Override
            public boolean isUnknown() {
                return true;
            }

            @Override
            public String getPath() {
                return "";
            }

        };
    }
}
