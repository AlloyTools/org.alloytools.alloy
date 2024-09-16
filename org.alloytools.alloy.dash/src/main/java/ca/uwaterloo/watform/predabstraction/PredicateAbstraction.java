package ca.uwaterloo.watform.predabstraction;

import ca.uwaterloo.watform.parser.DashModule;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

import ca.uwaterloo.watform.core.DashOptions;

public class PredicateAbstraction {

    // returns a deep copy of DashModule object
    public static DashModule copyDashModule(DashModule d){
        assert(d.hasRoot()); // there is a Dash component in this module

        try {
            // Method 1: This method needs DashModule to implement Serializable
            
            // ByteArrayOutputStream bos = new ByteArrayOutputStream();
            // ObjectOutputStream oos = new ObjectOutputStream(bos);
            // oos.writeObject(d);
            // oos.flush();
            // oos.close();
            // bos.close();
            // byte[] byteData = bos.toByteArray();

            // ByteArrayInputStream bais = new ByteArrayInputStream(byteData);
            // DashModule dcopy = new ObjectInputStream(bais).readObject();

            
            
            
            // Method 2: Also needs to implement Serializable, Apache Commons Lang

            // DashModule dcopy = org.apache.commons.lang.SerializationUtils.clone(d);




            // Method 3: Using Jackson; no need to implement Serializable

            // <T> T clone(T object, Class<T> clazzType) throws IOException {
            //     final ObjectMapper objMapper = new ObjectMapper();
            //     String jsonStr= objMapper.writeValueAsString(object);
            //     return objMapper.readValue(jsonStr, clazzType);
            //   }
            
        } catch(Exception e) {
            
        }
    }
}
