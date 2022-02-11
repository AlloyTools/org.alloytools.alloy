package org.alloytools.alloy.classic.test;

public class InstanceProxy<T> {

    //    final T proxy;
    //
    //    class TypeToInstance implements InvocationHandler {
    //
    //        @Override
    //        public Object invoke(Object proxy, Method method, Object[] args) throws Throwable {
    //
    //            return null;
    //        }
    //
    //    }
    //
    //
    //    public static <T> InstanceProxy<T> instance(Class<T> type, Instance instance) {
    //        assert type.isInterface() : "proxies only work for interfaces";
    //        if (instances == null)
    //            instances = Instance.empty();
    //        Proxy.newProxyInstance(type.getClassLoader(), new Class< ? >[] {
    //                                                                        type
    //        }, new TypeToInstance(instance));
    //    }
    //
    //
    //
    //    public T get() {
    //        return proxy;
    //    }
}
