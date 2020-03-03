
#include <oops/method.hpp>
#include <oops/methodData.hpp>
#include <utilities/json_serialization.hpp>

ProfilingDataSerializer ProfilingDataSerializer::_shared;
std::map<pstring, SerializatiedKlassList, std::less<pstring>, malloc_allocator<pstring> > SerializatiedKlassList::klass_name_map;


bool ProfilingDataSerializer::open(const char *fname) {
  assert(this->_file == NULL, "");
  this->_file = fopen(fname, "w");
  if(this->_file == NULL) {
    return false;
  }

  this->_first = true;

  fputs("[\n", this->_file);

  return true;
}

void ProfilingDataSerializer::close() {
  assert(this->_file != NULL, "");
  fputs("\n]", this->_file);
  fclose(this->_file);
  this->_file = NULL;
}

void ProfilingDataSerializer::serialize_method(Method *m) {
  assert(this->_file != NULL, "");

  if(this->_first) {
    this->_first = false;
  } else {
    fputs(",\n", this->_file);
  }

  MethodData *mdo = m->method_data();
  MethodCounters *mc = m->method_counters();
  if(mdo == NULL && mc == NULL) {
    return;
  }

  char method_name_buf[1024];
  Symbol *method_name = m->name();
  method_name->as_C_string(method_name_buf, sizeof(method_name_buf));

  char method_sig_buf[1024];
  Symbol *method_sig = m->signature();
  method_sig->as_C_string(method_sig_buf, sizeof(method_sig_buf));

  char klass_name_buf[1024];
  Symbol *klass_name = m->klass_name();
  klass_name->as_C_string(klass_name_buf, sizeof(klass_name_buf));

  const char*loader_name = m->method_holder()->class_loader_data()->loader_name();

  fprintf(this->_file, "  {\n"
                       "    \"klass\": \"%s\",\n"
                       "    \"name\": \"%s\",\n"
                       "    \"sig\": \"%s\",\n"
                       "    \"loader\": \"%s\",\n"
                       "    \"mdo\": ",
          klass_name_buf, method_name_buf, method_sig_buf, loader_name
      );

  if(mdo == NULL) {
    fputs("{ }", this->_file);
  } else {
    mdo->serialize_to_file(4, this->_file);
  }
  fputs(",\n    \"mco\": ", this->_file);

  if(mc == NULL) {
    fputs("{ }", this->_file);
  } else {
    mc->serialize_to_file(4, this->_file);
  }

  fprintf(this->_file, "\n  }");
}
