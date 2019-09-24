/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt;

import java.util.logging.Filter;
import java.util.logging.LogRecord;
import java.util.logging.Logger;

public class Alloy2SmtLogger implements Filter
{
    private final Logger LOGGER;
    
    public Alloy2SmtLogger(String className)
    {
        LOGGER = Logger.getLogger(className);                 
    }
    
    public void printInfo(String info) 
    {
        if(info != null) {
            LOGGER.info(info);
        }
    }
    
    public void printWarning(String warning) 
    {
        if(warning != null) {
            LOGGER.warning(warning);
        }
    }

    public void printSevere(String severe) 
    {
        if(severe != null) {
            LOGGER.warning(severe);
        }
    }    

    @Override
    public boolean isLoggable(LogRecord record) 
    {
        if(record == null)
        {
            return false;
        }
        return !record.getMessage().toLowerCase().startsWith("debug");
    }
    
    public enum LEVEL 
    {	        
        INFO ("info"),
        WARNING ("warning"),
        SEVERE ("severe");

        private final String levelStr;

        private LEVEL(String level) 
        {
            this.levelStr = level;
        }

        @Override
        public String toString() 
        {
            return this.levelStr;
        }    
    }       
}
