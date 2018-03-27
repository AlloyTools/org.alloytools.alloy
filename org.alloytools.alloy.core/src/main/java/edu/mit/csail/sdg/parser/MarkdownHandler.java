package edu.mit.csail.sdg.parser;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;
import java.util.HashMap;
import java.util.Map;

public class MarkdownHandler {

    enum State {
                TEXT {

                    @Override
                    State process(String line, Map<String,Object> yaml, StringBuilder sb) {
                        sb.append("\n");
                        if (line.equals("```alloy")) {
                            return ALLOY;
                        } else {
                            return TEXT;
                        }
                    }

                },
                YAML_START {

                    @Override
                    State process(String line, Map<String,Object> yaml, StringBuilder sb) {
                        if (!line.equals("---")) {
                            return null;
                        } else {
                            sb.append("\n");
                            return YAML;
                        }
                    }

                },
                YAML {

                    @Override
                    State process(String line, Map<String,Object> yaml, StringBuilder sb) {
                        sb.append("\n");
                        if (line.equals("---")) {
                            return TEXT;
                        } else {
                            return YAML;
                        }
                    }

                },
                ALLOY {

                    @Override
                    State process(String line, Map<String,Object> yaml, StringBuilder sb) {
                        if (line.startsWith("```")) {
                            sb.append("\n");
                            return TEXT;
                        } else {
                            sb.append(line).append("\n");
                            return ALLOY;
                        }
                    }
                };

        abstract State process(String line, Map<String,Object> yaml, StringBuilder sb);

    };

    public static String strip(String content) {
        try {
            State state = State.YAML_START;

            StringBuilder alloy = new StringBuilder();
            Map<String,Object> yaml = new HashMap<String,Object>();

            try (BufferedReader br = new BufferedReader(new StringReader(content))) {
                String line;
                while ((line = br.readLine()) != null) {
                    state = state.process(line, yaml, alloy);
                    if (state == null)
                        return content;
                }
            }
            return alloy.toString();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}
