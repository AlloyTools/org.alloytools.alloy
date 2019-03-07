


interface EventConstants {
    Key  EVENT_TOPIC                 = "event.topics";
    Key  EVENT_FILTER                = "event.filter";
    Key  EVENT_DELIVERY              = "event.delivery";
    Key  DELIVERY_ASYNC_ORDERED      = "async.ordered";
    Key  DELIVERY_ASYNC_UNORDERED    = "async.unordered";
    Key  BUNDLE_SIGNER               = "bundle.signer";
    Key  BUNDLE_SYMBOLICNAME         = "bundle.symbolicName";
    Key  BUNDLE_ID                   = "bundle.id";
    Key  BUNDLE                      = "bundle";
    Key  BUNDLE_VERSION              = "bundle.version";
    Key  EVENT                       = "event";
    Key  EXCEPTION                   = "exception";
    Key  EXCEPTION_CLASS             = "exception.class";
    Key  EXCEPTION_MESSAGE           = "exception.message";
    Key  MESSAGE                     = "message";
    Key  SERVICE                     = "service";
    Key  SERVICE_ID                  = Constants.SERVICE_ID;
    Key  SERVICE_OBJECTCLASS         = "service.objectClass";
    Key  SERVICE_PID                 = Constants.SERVICE_PID;
    Key  TIMESTAMP                   = "timestamp";
}


sig Topic(/(\/[a..zA..Z0-9])+/) {}
sig Key( /[a-zA-Z0-9._/ ) {}

interface Event {

    topic                           :   Topic;
    properties                      :   Key->Object;

    Object getProperty(Key name) {
        EVENT_TOPIC = name implies
            return topic;
        else
            containsProperty(name) implies
                return properties[name];
            else
                return null
    }

    boolean containsProperty(Key name) {
        EVENT_TOPIC = name implies {
            return true;
        } else
            return properties[name];
    }

    String[] getPropertyNames() {
        return domain[properties] + EVENT_TOPIC;
    }
    
    Map<Key,Object> getProperties() {
        return properties;
    }

    String getTopic() {
        return topic;
    }
}

service interface EventAdmin {

    handlers        : set EventHandler;

    void postEvent(Event event) {
	sometime deliver(event);
    }
    
    void sendEvent(Event event) {
        deliver(event)
    }
    
    
    private void deliver(Event event) {
        all h : filter(event) | h.handleEvent(event);
    }
    
    private set EventHandler filter(Event event) {
        { h : handlers | 
                event.topics in h.topics
            or 
                no h.filter
            or 
                h.filter.match(event.getProperties())
        } 
    }
    
    
}

service interface EventHandler {
    enum EventDelivery { ORDERED(EventConstants.DELIVERY_ASYNC_ORDERED), UNORDERED(EventConstants.DELIVERY_ASYNC_UNORDERED) }

    filter          = service.properties[EventConstants.EVENT_FILTER]   : lone Filter;
    topics          = service.properties[EventConstants.EVENT_TOPIC]    : set Topic;
    asyncDelivery   = service.properties[EventConstants.EVENT_DELIVERY] : EventDelivery;
    
    seq Event 	received;

    void handleEvent(Event event) {
	no asyncDelivery implies no e : range[received] | e.after(event)
	received' = received.add(event)
    }
}


abstract interface Filter {

    enum SimpleOp { EQ("="), LT("<"), GTE(">=") };    
    enum ComplexOp { AND("&"), OR("|"), NOT("!");
    
    interface SimpleExpr('(' key operator value ')') extends Filter {
    
        /[^=<>]+/      key;
        SimpleOp    	operator;
        /.*/      	value;  
        
        boolean match( Map<String,Object> map) {
            some v : map.get(key) {
                Object tmp = coerce(v.class, value);
                switch(operator) {
                case EQ:
                    return v = tmp;
                    
                case LT:
                    return v < tmp;
                    
                case GTE:
                    return v >= tmp;                
                }
            }
        }  
    }
    
    interface ComplexExpr( '(' operator subs ')' ) extends Filter {
        ComplexOp  operator;
        set Filter    subs;
        
        boolean match( Map<String,Object> map) {
            some v : map.get(key) {
                Object tmp = coerce(v.class, value);
                switch(operator) {
                case AND:
                    return all s : subs | s.match(map);
                    
                case OR:
                    return some s : subs | s.match(map);
                    
                case NOT:
                    return one s : subs | !s.match(map);                
                }
            }
        }  

    } {
        operator = NOT implies one subs else # subs >= 2
    }
    
    private T coerce( Class<T> c, String value);
}

interface Map<K,V> {

        interface Entry<K,V> {
            key         : K;
            value       : V;
            properties  : K lone -> V;

            K getKey();
            V getValue();
            V setValue(V v);
        } 

        var K lone -> V 		properties;

        V get(K key) {
            one properties[key] implies return properties[key] else return null; 
        }

        int size() {
            return # properties
        }

        V put( K key, V value) {
            properties' = properties + key->value
            return properties[key]
        }

        Set<K> keySet() {
            domain[properies]
        }

        List<V> values() {
            range[properies]
        }

        Iterator<Entry<K,V>> iterator() {

        }
}
