//
// Created by Perfare on 2020/7/4.
//

#include "il2cpp_dump.h"
#include <dlfcn.h>
#include <cstdlib>
#include <cstdio>
#include <unordered_set>
#include <cstring>
#include <cinttypes>
#include <string>
#include <vector>
#include <sstream>
#include <fstream>
#include <unistd.h>
#include <sys/types.h>
#include <algorithm>
#include "xdl.h"
#include "log.h"
#include "il2cpp-tabledefs.h"
#include "il2cpp-class.h"

#define DO_API(r, n, p) r (*n) p

#include "il2cpp-api-functions.h"

#undef DO_API

static uint64_t il2cpp_base = 0;

// Unity 2022 ARM64 registration: seven count/pointer pairs, then an unused pair.
// Locate and validate the type table; never call the assembly enumeration API.
struct RegistrationView {
    uint64_t address = 0;
    uint64_t types = 0;
    size_t typeCount = 0;
    size_t definitionCount = 0;
};
struct ReadableRange { uint64_t start, end; };

static uint64_t read_u64(uint64_t address) {
    uint64_t value;
    std::memcpy(&value, reinterpret_cast<const void *>(address), sizeof(value));
    return value;
}

static bool contains(const std::vector<ReadableRange> &ranges, uint64_t address, uint64_t size) {
    for (const auto &r : ranges) {
        if (address >= r.start && address < r.end && size <= r.end - address) return true;
    }
    return false;
}

static bool valid_type_kind(uint8_t kind) {
    return (kind >= 1 && kind <= 0x16) || kind == 0x18 || kind == 0x19 ||
           kind == 0x1b || kind == 0x1c || kind == 0x1d || kind == 0x1e;
}

static bool definition_type(uint8_t kind) {
    // Exclude constructed generics, arrays, pointers and generic parameters.
    return (kind >= 1 && kind <= 0x0e) || kind == 0x11 || kind == 0x12 ||
           kind == 0x16 || kind == 0x18 || kind == 0x19 || kind == 0x1c;
}

static bool scan_metadata_registration(const char *outDir, RegistrationView &result) {
    if (sizeof(void *) != 8) {
        LOGE("Registration layout currently supports 64-bit IL2CPP only");
        return false;
    }
    std::ifstream maps("/proc/self/maps");
    if (!maps) { LOGE("Cannot read process mappings"); return false; }
    std::vector<ReadableRange> ranges;
    std::string line;
    while (std::getline(maps, line)) {
        if (line.find("libil2cpp.so") == std::string::npos) continue;
        uint64_t start = 0, end = 0;
        char perms[5] = {};
        if (std::sscanf(line.c_str(), "%" SCNx64 "-%" SCNx64 " %4s", &start, &end, perms) == 3 &&
            end > start && perms[0] == 'r') ranges.push_back({start, end});
    }
    size_t candidates = 0;
    for (const auto &r : ranges) {
        if (r.end - r.start < 128) continue;
        for (uint64_t address = (r.start + 7) & ~uint64_t(7);
             address <= r.end - 128; address += 8) {
            uint64_t counts[7] = {}, pointers[7] = {};
            const uint64_t elementSizes[7] = {8, 8, 16, 8, 12, 8, 8};
            bool valid = true;
            for (size_t i = 0; i < 7; ++i) {
                counts[i] = read_u64(address + i * 16);
                pointers[i] = read_u64(address + i * 16 + 8);
                if (counts[i] < 1000 || counts[i] > 300000 ||
                    !contains(ranges, pointers[i], counts[i] * elementSizes[i])) {
                    valid = false;
                    break;
                }
            }
            if (!valid || counts[5] != counts[6] || counts[3] < counts[5] ||
                read_u64(address + 112) != 0 || read_u64(address + 120) != 0) continue;
            for (uint64_t i = 0; i < counts[3]; ++i) {
                auto type = read_u64(pointers[3] + i * 8);
                if (type % 8 != 0 || !contains(ranges, type, 16)) { valid = false; break; }
                auto bits = static_cast<uint32_t>(read_u64(type + 8));
                if (!valid_type_kind(static_cast<uint8_t>(bits >> 16))) { valid = false; break; }
            }
            if (!valid) continue;
            result = {address, pointers[3], static_cast<size_t>(counts[3]),
                      static_cast<size_t>(counts[5])};
            ++candidates;
        }
    }
    if (candidates != 1) {
        LOGE("Expected one validated registration, found %zu; refusing to guess", candidates);
        return false;
    }
    std::ofstream out(std::string(outDir) + "/files/metadata_registration.txt");
    out << "address=0x" << std::hex << result.address << "\n"
        << "types=0x" << result.types << "\n"
        << "type_count=" << std::dec << result.typeCount << "\n"
        << "definition_count=" << result.definitionCount << "\n";
    out.close();
    if (!out) LOGE("Cannot save registration report");
    LOGI("Validated registration: 0x%" PRIx64 ", types=%zu, definitions=%zu",
         result.address, result.typeCount, result.definitionCount);
    return true;
}

static bool api_ready = false;

void init_il2cpp_api(void *handle) {
#define DO_API(r, n, p) {                      \
    n = (r (*) p)xdl_sym(handle, #n, nullptr); \
    if(!n) {                                   \
        LOGW("api not found %s", #n);          \
    }                                          \
}

#include "il2cpp-api-functions.h"

#undef DO_API
}

std::string get_method_modifier(uint32_t flags) {
    std::stringstream outPut;
    auto access = flags & METHOD_ATTRIBUTE_MEMBER_ACCESS_MASK;
    switch (access) {
        case METHOD_ATTRIBUTE_PRIVATE:
            outPut << "private ";
            break;
        case METHOD_ATTRIBUTE_PUBLIC:
            outPut << "public ";
            break;
        case METHOD_ATTRIBUTE_FAMILY:
            outPut << "protected ";
            break;
        case METHOD_ATTRIBUTE_ASSEM:
        case METHOD_ATTRIBUTE_FAM_AND_ASSEM:
            outPut << "internal ";
            break;
        case METHOD_ATTRIBUTE_FAM_OR_ASSEM:
            outPut << "protected internal ";
            break;
    }
    if (flags & METHOD_ATTRIBUTE_STATIC) {
        outPut << "static ";
    }
    if (flags & METHOD_ATTRIBUTE_ABSTRACT) {
        outPut << "abstract ";
        if ((flags & METHOD_ATTRIBUTE_VTABLE_LAYOUT_MASK) == METHOD_ATTRIBUTE_REUSE_SLOT) {
            outPut << "override ";
        }
    } else if (flags & METHOD_ATTRIBUTE_FINAL) {
        if ((flags & METHOD_ATTRIBUTE_VTABLE_LAYOUT_MASK) == METHOD_ATTRIBUTE_REUSE_SLOT) {
            outPut << "sealed override ";
        }
    } else if (flags & METHOD_ATTRIBUTE_VIRTUAL) {
        if ((flags & METHOD_ATTRIBUTE_VTABLE_LAYOUT_MASK) == METHOD_ATTRIBUTE_NEW_SLOT) {
            outPut << "virtual ";
        } else {
            outPut << "override ";
        }
    }
    if (flags & METHOD_ATTRIBUTE_PINVOKE_IMPL) {
        outPut << "extern ";
    }
    return outPut.str();
}

bool _il2cpp_type_is_byref(const Il2CppType *type) {
    return type && il2cpp_type_is_byref(type);
}

std::string dump_method(Il2CppClass *klass) {
    std::stringstream outPut;
    outPut << "\n\t// Methods\n";
    void *iter = nullptr;
    while (auto method = il2cpp_class_get_methods(klass, &iter)) {
        //TODO attribute
        if (method->methodPointer) {
            outPut << "\t// RVA: 0x";
            outPut << std::hex << (uint64_t) method->methodPointer - il2cpp_base;
            outPut << " VA: 0x";
            outPut << std::hex << (uint64_t) method->methodPointer;
        } else {
            outPut << "\t// RVA: 0x VA: 0x0";
        }
        /*if (method->slot != 65535) {
            outPut << " Slot: " << std::dec << method->slot;
        }*/
        outPut << "\n\t";
        uint32_t iflags = 0;
        auto flags = il2cpp_method_get_flags(method, &iflags);
        outPut << get_method_modifier(flags);
        //TODO genericContainerIndex
        auto return_type = il2cpp_method_get_return_type(method);
        if (_il2cpp_type_is_byref(return_type)) {
            outPut << "ref ";
        }
        auto return_class = il2cpp_class_from_type(return_type);
        outPut << il2cpp_class_get_name(return_class) << " " << il2cpp_method_get_name(method)
               << "(";
        auto param_count = il2cpp_method_get_param_count(method);
        for (int i = 0; i < param_count; ++i) {
            auto param = il2cpp_method_get_param(method, i);
            auto attrs = il2cpp_type_get_attrs(param);
            if (_il2cpp_type_is_byref(param)) {
                if (attrs & PARAM_ATTRIBUTE_OUT && !(attrs & PARAM_ATTRIBUTE_IN)) {
                    outPut << "out ";
                } else if (attrs & PARAM_ATTRIBUTE_IN && !(attrs & PARAM_ATTRIBUTE_OUT)) {
                    outPut << "in ";
                } else {
                    outPut << "ref ";
                }
            } else {
                if (attrs & PARAM_ATTRIBUTE_IN) {
                    outPut << "[In] ";
                }
                if (attrs & PARAM_ATTRIBUTE_OUT) {
                    outPut << "[Out] ";
                }
            }
            auto parameter_class = il2cpp_class_from_type(param);
            outPut << il2cpp_class_get_name(parameter_class) << " "
                   << il2cpp_method_get_param_name(method, i);
            outPut << ", ";
        }
        if (param_count > 0) {
            outPut.seekp(-2, outPut.cur);
        }
        outPut << ") { }\n";
        //TODO GenericInstMethod
    }
    return outPut.str();
}

std::string dump_property(Il2CppClass *klass) {
    std::stringstream outPut;
    outPut << "\n\t// Properties\n";
    void *iter = nullptr;
    while (auto prop_const = il2cpp_class_get_properties(klass, &iter)) {
        //TODO attribute
        auto prop = const_cast<PropertyInfo *>(prop_const);
        auto get = il2cpp_property_get_get_method(prop);
        auto set = il2cpp_property_get_set_method(prop);
        auto prop_name = il2cpp_property_get_name(prop);
        outPut << "\t";
        Il2CppClass *prop_class = nullptr;
        uint32_t iflags = 0;
        if (get) {
            outPut << get_method_modifier(il2cpp_method_get_flags(get, &iflags));
            prop_class = il2cpp_class_from_type(il2cpp_method_get_return_type(get));
        } else if (set) {
            outPut << get_method_modifier(il2cpp_method_get_flags(set, &iflags));
            auto param = il2cpp_method_get_param(set, 0);
            prop_class = il2cpp_class_from_type(param);
        }
        if (prop_class) {
            outPut << il2cpp_class_get_name(prop_class) << " " << prop_name << " { ";
            if (get) {
                outPut << "get; ";
            }
            if (set) {
                outPut << "set; ";
            }
            outPut << "}\n";
        } else {
            if (prop_name) {
                outPut << " // unknown property " << prop_name;
            }
        }
    }
    return outPut.str();
}

std::string dump_field(Il2CppClass *klass) {
    std::stringstream outPut;
    outPut << "\n\t// Fields\n";
    auto is_enum = il2cpp_class_is_enum(klass);
    void *iter = nullptr;
    while (auto field = il2cpp_class_get_fields(klass, &iter)) {
        //TODO attribute
        outPut << "\t";
        auto attrs = il2cpp_field_get_flags(field);
        auto access = attrs & FIELD_ATTRIBUTE_FIELD_ACCESS_MASK;
        switch (access) {
            case FIELD_ATTRIBUTE_PRIVATE:
                outPut << "private ";
                break;
            case FIELD_ATTRIBUTE_PUBLIC:
                outPut << "public ";
                break;
            case FIELD_ATTRIBUTE_FAMILY:
                outPut << "protected ";
                break;
            case FIELD_ATTRIBUTE_ASSEMBLY:
            case FIELD_ATTRIBUTE_FAM_AND_ASSEM:
                outPut << "internal ";
                break;
            case FIELD_ATTRIBUTE_FAM_OR_ASSEM:
                outPut << "protected internal ";
                break;
        }
        if (attrs & FIELD_ATTRIBUTE_LITERAL) {
            outPut << "const ";
        } else {
            if (attrs & FIELD_ATTRIBUTE_STATIC) {
                outPut << "static ";
            }
            if (attrs & FIELD_ATTRIBUTE_INIT_ONLY) {
                outPut << "readonly ";
            }
        }
        auto field_type = il2cpp_field_get_type(field);
        auto field_class = il2cpp_class_from_type(field_type);
        outPut << il2cpp_class_get_name(field_class) << " " << il2cpp_field_get_name(field);
        //TODO 获取构造函数初始化后的字段值
        if (attrs & FIELD_ATTRIBUTE_LITERAL && is_enum) {
            uint64_t val = 0;
            il2cpp_field_static_get_value(field, &val);
            outPut << " = " << std::dec << val;
        }
        outPut << "; // 0x" << std::hex << il2cpp_field_get_offset(field) << "\n";
    }
    return outPut.str();
}

std::string dump_type(Il2CppClass *klass) {
    std::stringstream outPut;
    outPut << "\n// Namespace: " << il2cpp_class_get_namespace(klass) << "\n";
    auto flags = il2cpp_class_get_flags(klass);
    if (flags & TYPE_ATTRIBUTE_SERIALIZABLE) {
        outPut << "[Serializable]\n";
    }
    //TODO attribute
    auto is_valuetype = il2cpp_class_is_valuetype(klass);
    auto is_enum = il2cpp_class_is_enum(klass);
    auto visibility = flags & TYPE_ATTRIBUTE_VISIBILITY_MASK;
    switch (visibility) {
        case TYPE_ATTRIBUTE_PUBLIC:
        case TYPE_ATTRIBUTE_NESTED_PUBLIC:
            outPut << "public ";
            break;
        case TYPE_ATTRIBUTE_NOT_PUBLIC:
        case TYPE_ATTRIBUTE_NESTED_FAM_AND_ASSEM:
        case TYPE_ATTRIBUTE_NESTED_ASSEMBLY:
            outPut << "internal ";
            break;
        case TYPE_ATTRIBUTE_NESTED_PRIVATE:
            outPut << "private ";
            break;
        case TYPE_ATTRIBUTE_NESTED_FAMILY:
            outPut << "protected ";
            break;
        case TYPE_ATTRIBUTE_NESTED_FAM_OR_ASSEM:
            outPut << "protected internal ";
            break;
    }
    if (flags & TYPE_ATTRIBUTE_ABSTRACT && flags & TYPE_ATTRIBUTE_SEALED) {
        outPut << "static ";
    } else if (!(flags & TYPE_ATTRIBUTE_INTERFACE) && flags & TYPE_ATTRIBUTE_ABSTRACT) {
        outPut << "abstract ";
    } else if (!is_valuetype && !is_enum && flags & TYPE_ATTRIBUTE_SEALED) {
        outPut << "sealed ";
    }
    if (flags & TYPE_ATTRIBUTE_INTERFACE) {
        outPut << "interface ";
    } else if (is_enum) {
        outPut << "enum ";
    } else if (is_valuetype) {
        outPut << "struct ";
    } else {
        outPut << "class ";
    }
    outPut << il2cpp_class_get_name(klass); //TODO genericContainerIndex
    std::vector<std::string> extends;
    auto parent = il2cpp_class_get_parent(klass);
    if (!is_valuetype && !is_enum && parent) {
        auto parent_type = il2cpp_class_get_type(parent);
        if (parent_type->type != IL2CPP_TYPE_OBJECT) {
            extends.emplace_back(il2cpp_class_get_name(parent));
        }
    }
    void *iter = nullptr;
    while (auto itf = il2cpp_class_get_interfaces(klass, &iter)) {
        extends.emplace_back(il2cpp_class_get_name(itf));
    }
    if (!extends.empty()) {
        outPut << " : " << extends[0];
        for (int i = 1; i < extends.size(); ++i) {
            outPut << ", " << extends[i];
        }
    }
    outPut << "\n{";
    outPut << dump_field(klass);
    outPut << dump_property(klass);
    outPut << dump_method(klass);
    //TODO EventInfo
    outPut << "}\n";
    return outPut.str();
}

void il2cpp_api_init(void *handle) {
    api_ready = false;
    LOGI("il2cpp_handle: %p", handle);
    init_il2cpp_api(handle);
    if (!il2cpp_domain_get || !il2cpp_thread_attach) {
        LOGE("Required initialization APIs are missing");
        return;
    }
    Dl_info info{};
    if (!dladdr(reinterpret_cast<void *>(il2cpp_domain_get), &info) || !info.dli_fbase) {
        LOGE("Cannot resolve il2cpp base");
        return;
    }
    il2cpp_base = reinterpret_cast<uint64_t>(info.dli_fbase);
    LOGI("il2cpp_base: %" PRIx64, il2cpp_base);
    for (int i = 0; i < 30; ++i) {
        auto domain = il2cpp_domain_get();
        if (domain) {
            LOGI("il2cpp domain ready: %p", static_cast<void *>(domain));
            auto thread = il2cpp_thread_attach(domain);
            LOGI("il2cpp thread attached: %p", static_cast<void *>(thread));
            api_ready = thread != nullptr;
            return;
        }
        sleep(1);
    }
    LOGE("il2cpp domain timeout");
}

void il2cpp_dump(const char *outDir) {
    LOGI("Registration dump v2: assembly enumeration disabled");
    if (!outDir || !api_ready) { LOGE("Cannot dump: initialization failed"); return; }
#define REQUIRE_API(name) if (!name) { LOGE("Required dump API missing: %s", #name); return; }
    REQUIRE_API(il2cpp_class_from_type);
    REQUIRE_API(il2cpp_class_get_fields);
    REQUIRE_API(il2cpp_class_get_flags);
    REQUIRE_API(il2cpp_class_get_image);
    REQUIRE_API(il2cpp_class_get_interfaces);
    REQUIRE_API(il2cpp_class_get_methods);
    REQUIRE_API(il2cpp_class_get_name);
    REQUIRE_API(il2cpp_class_get_namespace);
    REQUIRE_API(il2cpp_class_get_parent);
    REQUIRE_API(il2cpp_class_get_properties);
    REQUIRE_API(il2cpp_class_get_type);
    REQUIRE_API(il2cpp_class_is_enum);
    REQUIRE_API(il2cpp_class_is_valuetype);
    REQUIRE_API(il2cpp_field_get_flags);
    REQUIRE_API(il2cpp_field_get_name);
    REQUIRE_API(il2cpp_field_get_offset);
    REQUIRE_API(il2cpp_field_get_type);
    REQUIRE_API(il2cpp_field_static_get_value);
    REQUIRE_API(il2cpp_image_get_name);
    REQUIRE_API(il2cpp_method_get_flags);
    REQUIRE_API(il2cpp_method_get_name);
    REQUIRE_API(il2cpp_method_get_param);
    REQUIRE_API(il2cpp_method_get_param_count);
    REQUIRE_API(il2cpp_method_get_param_name);
    REQUIRE_API(il2cpp_method_get_return_type);
    REQUIRE_API(il2cpp_property_get_get_method);
    REQUIRE_API(il2cpp_property_get_name);
    REQUIRE_API(il2cpp_property_get_set_method);
    REQUIRE_API(il2cpp_type_get_attrs);
    REQUIRE_API(il2cpp_type_is_byref);
#undef REQUIRE_API
    RegistrationView registration;
    if (!scan_metadata_registration(outDir, registration)) return;
    const auto finalPath = std::string(outDir) + "/files/dump.cs";
    const auto partialPath = finalPath + ".partial";
    std::ofstream out(partialPath, std::ios::trunc);
    if (!out) { LOGE("Cannot open partial dump file"); return; }
    out << "// IL2CPP dump via validated registration type table.\n"
        << "// Constructed generic types, arrays and generic parameters are excluded.\n"
        << "// Registered definitions: " << registration.definitionCount << "\n";
    std::unordered_set<Il2CppClass *> seen;
    size_t written = 0, unresolved = 0;
    for (size_t i = 0; i < registration.typeCount; ++i) {
        auto address = read_u64(registration.types + i * 8);
        auto bits = static_cast<uint32_t>(read_u64(address + 8));
        if (!definition_type(static_cast<uint8_t>(bits >> 16))) continue;
        // Flush the index before APIs so an interrupted dump identifies the last entry.
        out << "\n// Type table index: " << i << "\n";
        out.flush();
        if (!out) { LOGE("Partial dump write failed"); return; }
        auto type = reinterpret_cast<const Il2CppType *>(address);
        auto klass = il2cpp_class_from_type(type);
        if (!klass) { ++unresolved; continue; }
        if (!seen.insert(klass).second) continue;
        auto image = il2cpp_class_get_image(klass);
        auto imageName = image ? il2cpp_image_get_name(image) : nullptr;
        if (!imageName) { LOGE("Class has no image at index %zu", i); return; }
        out << "// Dll : " << imageName << "\n";
        out << dump_type(klass);
        out.flush();
        if (!out) { LOGE("Partial dump write failed"); return; }
        ++written;
        if (written == 1 || written % 128 == 0) {
            LOGI("Registration dump progress: %zu classes, table index %zu/%zu",
                 written, i + 1, registration.typeCount);
        }
    }
    out << "\n// Traversal ended: " << written << " classes; " << unresolved << " unresolved entries.\n";
    out.close();
    if (!out || written == 0 || unresolved != 0 || written != registration.definitionCount) {
        LOGE("Incomplete dump retained at %s: %zu/%zu classes, %zu unresolved entries",
             partialPath.c_str(), written, registration.definitionCount, unresolved);
        return;
    }
    if (std::rename(partialPath.c_str(), finalPath.c_str()) != 0) {
        LOGE("Cannot rename partial dump to %s", finalPath.c_str());
        return;
    }
    LOGI("Dump finished: %zu classes, %s", written, finalPath.c_str());
}
