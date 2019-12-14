package se.src.alloy.cli;

import java.io.FileReader;
import java.io.IOException;
import java.util.Properties;

public class Config {
  public static final String DEFAULT_CONFIG_FILE = ".alloy";
  public static final Boolean DEFAULT_WATCH_MODE = false;
  private final Verbosity verbosity;

  private Config(Verbosity verbosity) {
    this.verbosity = verbosity;
  }

  public static Config fromFile(String configFile) throws IOException {
    final FileReader reader = new FileReader(configFile);
    Properties properties = new Properties();
    properties.load(reader);

    Verbosity verbosity =
        Verbosity.valueOf(String.valueOf(properties.get(Keys.VERBOSITY)).toUpperCase());

    return new Config(verbosity);
  }

  public Verbosity verbosity() {
    return verbosity;
  }

  enum Verbosity {
    HIGH,
    LOW
  }

  public class Keys {
    public static final String VERBOSITY = "verbosity";
  }
}
